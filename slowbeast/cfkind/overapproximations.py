from functools import partial

from slowbeast.solvers.symcrete import IncrementalSolver
from slowbeast.symexe.annotations import (
    AssertAnnotation,
    execute_annotation_substitutions,
)
from slowbeast.symexe.statesset import StatesSet, union, intersection, complement
from slowbeast.util.debugging import dbg, dbgv
from ..core.executionresult import PathExecutionResult
from ..domains.concrete_bitvec import ConcreteBitVec
from ..domains.exprmgr import em_optimize_expressions
from ..solvers.symcrete import global_expr_mgr


def remove_implied_literals(clauses):
    """
    Returns an equivalent but possibly smaller formula
    """

    solver = IncrementalSolver()

    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in clauses:
        if c.is_concrete() and c.value() is True:
            continue
        if c.is_or():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)
            solver.add(c)

    EM = global_expr_mgr()
    Not = EM.Not
    newclauses = []
    # NOTE: we could do this until a fixpoint, but...
    for r in rest:
        changed = False
        drop = False
        newc = []
        for l in r.children():
            if solver.is_sat(l) is False:
                # dbg(f"Dropping {l}, it's False")
                changed = True
            elif solver.is_sat(Not(l)) is False:
                # XXX: is it worth querying the solver for this one?
                drop = True
                break
            else:
                newc.append(l)
        if drop:
            # dbg(f"Dropping {r}, it's True")
            continue
        if changed:
            if len(newc) == 1:
                singletons.append(newc[0])
                solver.add(newc[0])
            else:
                newclauses.append(EM.disjunction(*newc))
        else:
            newclauses.append(r)

    return singletons + newclauses


def poststates(executor, paths, prestate):
    """
    Return states after executing paths with precondition 'pre'
    extended by the postcondition 'post'. We do not evaluate the
    validity of the postcondition, so that we can get the path condition
    and manipulate with it (it can be unsat and evaluating it could
    simplify it to false, which is undesired here
    """
    result = PathExecutionResult()
    indexecutor = executor.ind_executor()
    for path in paths:
        # p = path.copy()
        # the post-condition is the whole frame
        # if pre:
        #    p.add_annot_before(pre.as_assume_annotation())

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = indexecutor.execute_annotated_path([prestate.copy()], path)
        result.merge(r)

    assert result.errors is None
    if not result.ready:
        return None

    ready = result.ready
    return ready


def literals(c):
    if c.is_or():
        yield from c.children()
    else:
        yield c


def get_predicate(l):
    EM = global_expr_mgr()
    if l.is_sle():
        return EM.Le
    if l.is_sge():
        return EM.Ge
    if l.is_slt():
        return EM.Lt
    if l.is_sgt():
        return EM.Gt
    if l.is_ule():
        return partial(EM.Le, unsigned=True)
    if l.is_uge():
        return partial(EM.Ge, unsigned=True)
    if l.is_ult():
        return partial(EM.Lt, unsigned=True)
    if l.is_ugt():
        return partial(EM.Gt, unsigned=True)

    raise NotImplementedError(f"Unhandled predicate in expr {l}")


def _decompose_literal(l):
    isnot = False
    if l.is_not():
        isnot = True
        l = list(l.children())[0]

    if l.is_lt() or l.is_le():
        addtoleft = False
    elif l.is_gt() or l.is_ge():
        addtoleft = True
    else:
        return None, None, None, None

    chld = list(l.children())
    assert len(chld) == 2
    left, P, right = chld[0], get_predicate(l), chld[1]

    if isnot:
        addtoleft = not addtoleft
        EM = global_expr_mgr()
        binop = P

        def P(a, b):
            return EM.Not(binop(a, b))

    return left, right, P, addtoleft


class DecomposedLiteral:
    __slots__ = "left", "right", "pred", "addtoleft"

    def __init__(self, lit) -> None:
        self.left, self.right, self.pred, self.addtoleft = _decompose_literal(lit)

    def __bool__(self) -> bool:
        assert self.left is None or self.right and self.pred
        return self.left is not None

    def toformula(self):
        return self.pred(self.left, self.right)

    def bitwidth(self):
        left = self.left
        if left:
            return left.type().bitwidth()
        return None

    def extended(self, num):
        expr_mgr = global_expr_mgr()
        left, right = self.left, self.right
        if self.addtoleft:
            left = expr_mgr.Add(left, num)
        else:
            right = expr_mgr.Add(right, num)

        # try pushing further
        return self.pred(left, right)


def get_left_right(l):
    if l.is_not():
        l = list(l.children())[0]

    chld = list(l.children())
    assert len(chld) == 2, "Invalid literal (we assume binop or not(binop)"
    return chld[0], chld[1]


class LoopStateOverapproximation:
    """
    Structure taking care for over-approximations of states
    """

    # __slots__ = "executor", "clauses", "target", "unsafe", "loop", "expr_mgr"

    def __init__(self, S, executor, target, unsafe, loop, expr_mgr) -> None:
        self.executor = executor
        self.target = target
        self.unsafe = unsafe
        self.loop = loop
        self.expr_mgr = expr_mgr

        self.goal = S
        # clauses are our internal working structure. Any change that we do is not visible until we do commit().
        # Note: break equalities to <= && >= so that we can overapproximate
        # them
        self.clauses = list(S.as_expr().rewrite_and_simplify().to_cnf().children())

        safesolver = IncrementalSolver()
        safesolver.add(unsafe.as_expr())
        self.safesolver = safesolver

    def _drop_clauses(self, clauses, assumptions):
        """
        assumptions are clauses that we do not try to drop
        """
        expressions = set()
        for c in clauses:
            if c.is_concrete():
                if c.value() is False:
                    dbg("  ... got FALSE in clauses, returning FALSE")
                    return [self.expr_mgr.get_false()]
                dbg("  ... dropping True clause")
            else:
                expressions.add(c)

        newclauses = list(expressions)
        drop_clause = self.drop_clause
        for clause in expressions:
            newclauses = drop_clause(clause, newclauses, assumptions)
        return newclauses

    def drop_clause(self, clause, clauses, assumptions):
        """
        Try dropping the clause. If successful, return a list of new clauses.
        DO NOT modify 'clauses' parameter!.
        """
        assert not clause.is_concrete(), clause
        # create a temporary formula without the given clause
        tmpclauses = clauses.copy()
        tmpclauses.remove(clause)

        # check whether we can get rid of the clause
        if assumptions:
            tmpexpr = self.expr_mgr.conjunction(*tmpclauses, assumptions.as_expr())
        else:
            tmpexpr = self.expr_mgr.conjunction(*tmpclauses)
        if tmpexpr.is_concrete():
            return (
                clauses  # either False or True are bad for us, return original clauses
            )

        # == safety check
        if self.safesolver.is_sat(tmpexpr) is not False:
            return clauses  # unsafe overapprox, do not drop

        # == inductiveness check
        X = self.goal.copy()
        X.reset_expr(tmpexpr)
        if self.loop.set_is_inductive_towards(X, self.target):
            dbg(f"  dropped {clause}...")
            return tmpclauses
        return clauses

    def _drop_clauses_fixpoint(self, assumptions):
        """Drop clauses until fixpoint"""
        newclauses = self.clauses
        _drop_clauses = self._drop_clauses
        while True:
            dbgv(" ... droping clauses (starting iteration)")
            oldlen = len(newclauses)
            newclauses = _drop_clauses(newclauses, assumptions)
            if oldlen == len(newclauses):
                break
        dbgv(" ... done droping clauses")
        return newclauses

    def drop_clauses(self, assumptions=None) -> None:
        newclauses = self._drop_clauses_fixpoint(assumptions)
        # now add the assumptions if we used them (without them the formula is
        # not equivalent to expr after dropping the clauses)
        if assumptions:
            newclauses.extend(list(assumptions.as_cnf_expr().children()))
        clauses = remove_implied_literals(newclauses)

        assert intersection(
            self.unsafe, self.executor.create_set(self.expr_mgr.conjunction(*clauses))
        ).is_empty(), f"Dropping clauses made the set unsafe:\n{self.clauses}\nvvv new clauses vvv\n{clauses}\nvvv with unsafe vvv:\n{self.unsafe}"
        self.clauses = clauses

    def commit(self):
        S = self.goal
        expr = self.expr_mgr.conjunction(*self.clauses)
        if not expr.is_concrete():
            expr = expr.rewrite_and_simplify()
        S.reset_expr(expr)
        return S

    def overapproximate(self) -> None:
        conjunction = self.expr_mgr.conjunction
        overapprox_clause = self.overapprox_clause
        clauses, newclauses = self.clauses, []
        target = self.target
        S = self.goal
        em = self.expr_mgr
        Le, Ge = em.Le, em.Ge
        Lt, Gt = em.Lt, em.Gt
        # Now take every clause c and try to overapproximate it
        for n in range(len(clauses)):
            c = clauses[n]
            # R is the rest of the actual formula without the clause c
            R = S.copy()  # copy the substitutions
            R.reset_expr(conjunction(*newclauses, *clauses[n + 1 :]))

            # try breaking equalities into inequalities. We do it here so that we preserve the equality
            # if we fail overapproximating. This is because when we later derive relations from path condition,
            # we want the equalities there.
            if c.is_eq():
                chld = list(c.children())
                assert len(chld) == 2, c
                le = Le(chld[0], chld[1])
                ge = Ge(chld[0], chld[1])
                new_le = overapprox_clause(le, intersection(R, ge))
                new_ge = overapprox_clause(ge, intersection(R, le))
                if (
                    new_le
                    and new_ge
                    and (new_le != le or new_ge != ge)
                    and is_overapprox_of(S, intersection(R, new_le, new_ge))
                ):
                    newclauses.append(new_le)
                    newclauses.append(new_ge)
                    continue
                if (
                    new_le
                    and new_le != le
                    and is_overapprox_of(S, intersection(R, new_le, ge))
                ):
                    newclauses.append(new_le)
                    newclauses.append(ge)
                    continue
                if (
                    new_ge
                    and new_ge != ge
                    and is_overapprox_of(S, intersection(R, new_ge, le))
                ):
                    newclauses.append(new_ge)
                    newclauses.append(le)
                    continue
                newclauses.append(c)
            elif c.is_not() and next(c.children()).is_eq():
                chld = list(next(c.children()).children())
                assert len(chld) == 2, c
                lt = Lt(chld[0], chld[1])
                gt = Gt(chld[0], chld[1])
                new_lt = (
                    overapprox_clause(lt, R)
                    if self.loop.set_is_inductive_towards(
                        intersection(R, lt), target, allow_infeasible_only=True
                    )
                    else em.get_false()
                )
                new_gt = (
                    overapprox_clause(gt, R)
                    if self.loop.set_is_inductive_towards(
                        intersection(R, gt), target, allow_infeasible_only=True
                    )
                    else em.get_false()
                )
                if (
                    new_lt
                    and new_gt
                    and (new_lt != lt or new_gt != gt)
                    and is_overapprox_of(S, intersection(R, em.Or(new_lt, new_gt)))
                ):
                    newclauses.append(em.Or(new_lt, new_gt))
                    continue
                if (
                    new_lt
                    and new_lt != lt
                    and is_overapprox_of(S, intersection(R, em.Or(new_lt, gt)))
                ):
                    newclauses.append(em.Or(new_lt, gt))
                    continue
                if (
                    new_gt
                    and new_gt != gt
                    and is_overapprox_of(S, intersection(R, em.Or(new_gt, lt)))
                ):
                    newclauses.append(em.Or(new_gt, lt))
                    continue
                newclauses.append(c)
            else:
                newclause = overapprox_clause(c, R)
                if newclause:
                    # newclauses.append(newclause)
                    # FIXME: this check should be
                    # assertion, overapprox_clause should not give us such clauses
                    # assert intersection(tmp, S).is_empty()
                    if is_overapprox_of(S, intersection(R, newclause)):
                        # new clause makes S to be an overapproximation, good
                        newclauses.append(newclause)
                    else:
                        newclauses.append(c)
                else:
                    newclauses.append(c)

            if __debug__:
                R.intersect(newclauses[-1])
                assert not R.is_empty()
                R.intersect(self.unsafe)
                assert R.is_empty(), f"Overapproxmating clause made the set unsafe: {c}"

        if __debug__:
            S.reset_expr(self.expr_mgr.conjunction(*newclauses))
            assert not S.is_empty()
            assert intersection(
                self.unsafe, S
            ).is_empty(), "Overapproxmating clauses made the set unsafe"

        self.clauses = newclauses

    def overapprox_clause(self, c, R: StatesSet):
        """
        c - the clause
        R - rest of clauses of the formula
        """
        if c.is_concrete():
            return c

        assert intersection(R, c, self.unsafe).is_empty(), f"{R} & {c} & {self.unsafe}"
        if __debug__:
            X = R.copy()
            X.intersect(c)
            assert self.loop.set_is_inductive_towards(
                X, self.target, allow_infeasible_only=True
            ), X

        newc = []
        lits = list(literals(c))
        simplify = self.expr_mgr.simplify

        overapprox_lit = self.overapprox_literal
        for l in lits:
            newl = simplify(overapprox_lit(l, lits, R))
            newc.append(newl)
            if __debug__:
                if l != newl:
                    dbg(
                        f"  Overapproximated {l} --> {newl}",
                        color="gray",
                    )
                    X = R.copy()
                    X.intersect(
                        self.expr_mgr.disjunction(
                            *(
                                newc[i] if i < len(newc) else lits[i]
                                for i in range(len(lits))
                            )
                        )
                    )
                    assert self.loop.set_is_inductive_towards(
                        X, self.target, allow_infeasible_only=True
                    ), f"X: {X}, target: {self.target}"

        if len(newc) == 1:
            return newc[0]

        return self.expr_mgr.disjunction(*newc)

    def overapprox_literal(self, l, rl, S: StatesSet):
        """
        l - literal
        rl - list of all literals in the clause
        S - rest of clauses of the formula except for 'rl'
        unsafe - set of unsafe states
        target - set of safe states that we want to keep reachable
        """
        assert not l.is_and() and not l.is_or(), f"Input is not a literal: {l}"
        assert intersection(S, l, self.unsafe).is_empty(), "Unsafe states in input"

        expr_mgr = self.expr_mgr
        executor = self.executor

        # create a fresh literal that we use as a placeholder instead of our
        # literal during extending
        placeholder = expr_mgr.symbolic_bool("litext")
        # X is the original formula with 'placeholder' instead of 'l'
        clause_without_lit = list(x for x in rl if x != l)
        X = intersection(S, expr_mgr.disjunction(placeholder, *clause_without_lit))
        assert not X.is_empty(), f"S: {S}, l: {l}, rl: {rl}"
        post = poststates(executor, self.loop.paths(), X.get_se_state())
        if not post:
            return l

        # U is allowed reachable set of states
        U = union(self.target, X)
        indset_with_placeholder = U.as_assume_annotation()
        # execute the instructions from annotations, so that the substitutions
        # have up-to-date value
        poststates_with_placeholder, nonr = execute_annotation_substitutions(
            executor.ind_executor(), post, indset_with_placeholder
        )
        assert not nonr, f"Got errors while processing annotations: {nonr}"

        dliteral = DecomposedLiteral(l)
        if not dliteral:
            return l
        assert dliteral.toformula() == l

        # we always check S && unsafe && new_clause, so we can keep S  and unsafe
        # in the solver all the time
        safety_solver = self.safesolver
        safety_solver.push()
        safety_solver.add(S.as_expr())
        # induction solver
        solver = IncrementalSolver()

        ldata = LiteralOverapproximationData(
            l,
            dliteral,
            rl,
            clause_without_lit,
            indset_with_placeholder,
            placeholder,
            safety_solver,
            solver,
            poststates_with_placeholder,
        )
        assert isinstance(ldata.decomposed_literal, DecomposedLiteral)

        em_optimize_expressions(False)
        # the optimizer could make And or Or from the literal, we do not want
        # that...
        l = self.extend_literal(ldata)
        em_optimize_expressions(True)

        safety_solver.pop()
        return l

    def extend_literal(self, ldata):
        dliteral = ldata.decomposed_literal

        bw = dliteral.bitwidth()
        two = ConcreteBitVec(2, bw)
        # adding 2 ** bw would be like adding 0, stop before that
        maxnum = 2**bw - 1

        # a fast path where we try shift just by one.  If we cant, we can give up
        # FIXME: try more low values (e.g., to 10)
        num = ConcreteBitVec(1, bw)
        l = dliteral.extended(num)
        if not self.check_literal(l, ldata):
            return ldata.literal

        # this is the final number that we are going to add to one side of the
        # literal
        finalnum = ConcreteBitVec(1, bw)  # we know we can add 1 now
        num = ConcreteBitVec(2 ** (bw - 1) - 1, bw)  # this num we'll try to add
        extend_with_num = self.extend_with_num
        expr_mgr = self.expr_mgr
        Div = expr_mgr.Div
        while finalnum.value() <= maxnum:
            finalnum = extend_with_num(dliteral, finalnum, num, maxnum, ldata)

            if num.value() <= 1:
                # we have added also as many 1 as we could, finish
                return dliteral.extended(finalnum)
            num = Div(num, two)
        raise RuntimeError("Unreachable")

    def check_literal(self, lit, ldata) -> bool:
        if lit is None or lit.is_concrete():
            return False

        expr_mgr = self.expr_mgr
        # safety check
        if (
            not ldata.safety_solver.try_is_sat(
                500, expr_mgr.disjunction(lit, *ldata.clause)
            )
            is False
        ):
            return False

        have_feasible = False
        substitute = expr_mgr.substitute

        I = ldata.indset_with_placeholder
        placeholder = ldata.placeholder
        solver = ldata.solver
        A = AssertAnnotation(
            substitute(I.expr(), (placeholder, lit)), I.substitutions(), expr_mgr
        )
        for s in ldata.loop_poststates:
            # feasability check
            solver.push()
            pathcond = substitute(s.path_condition(), (placeholder, lit))
            solver.add(pathcond)
            feasible = solver.try_is_sat(500)
            if feasible is not True:
                solver.pop()
                if feasible is None:  # solver t-outed/failed
                    return False
                continue
            # feasible means ok, but we want at least one feasible path
            # FIXME: do we?
            have_feasible = True

            # inductivity check
            hasnocti = A.do_substitutions(s)
            # we have got pathcond in solver already
            if (
                solver.try_is_sat(500, expr_mgr.Not(hasnocti)) is not False
            ):  # there exist CTI
                solver.pop()
                return False
            solver.pop()
        return have_feasible

    def extend_with_num(self, dliteral, constadd, num, maxnum, ldata):
        """
        Add 'num' as many times as possible to the literal that is created from dliteral and constadd

        constadd - this number is always added to the literal (that is the current
                   value of extending
        num - number to keep adding
        maxnum - maximal number to try (the sum of added 'num' cannot exceed this)

        \return the maximal added number which is multiple of 'num' + constadd,
                i.e., the new value that is safe to add to the literal
        """
        numval = num.value()
        retval = constadd
        Add = self.expr_mgr.Add

        # keep the retval also in python int, so that we can check it agains
        # maxnum (expressions are counted modulo, so we cannot check that
        # on expressions)
        acc = retval.value() + numval
        if acc > maxnum:
            return retval

        newretval = Add(retval, num)
        newl = dliteral.extended(newretval)

        # push as far as we can with this num
        check_literal = self.check_literal
        while check_literal(newl, ldata):
            # the tried value is ok, so set it as the new final value
            retval = newretval
            assert retval.value() <= maxnum

            newretval = Add(newretval, num)
            acc += numval

            # do not try to shift the number beyond maxnum
            if acc > maxnum:
                break
            newl = dliteral.extended(newretval)

        return retval


class LiteralOverapproximationData:
    __slots__ = (
        "literal",
        "decomposed_literal",
        "clause",
        "clause_without_literal",
        "indset_with_placeholder",
        "placeholder",
        "safety_solver",
        "solver",
        "loop_poststates",
    )

    def __init__(
        self,
        literal,
        dliteral: DecomposedLiteral,
        clause,
        clause_without_literal,
        indset_with_placeholder,
        placeholder,
        safety_solver: IncrementalSolver,
        solver: IncrementalSolver,
        loop_poststates,
    ) -> None:
        assert isinstance(dliteral, DecomposedLiteral)
        assert isinstance(clause, list)
        assert isinstance(clause_without_literal, list)
        assert isinstance(solver, IncrementalSolver)
        assert isinstance(safety_solver, IncrementalSolver)

        self.literal = literal
        self.decomposed_literal = dliteral
        self.clause = clause
        self.clause_without_literal = clause_without_literal
        self.indset_with_placeholder = indset_with_placeholder
        self.placeholder = placeholder
        self.safety_solver = safety_solver
        self.solver = solver
        # also with placeholder
        self.loop_poststates = loop_poststates


def is_overapprox_of(A, B: StatesSet) -> bool:
    """Return true if B is overapproximation of A"""
    return intersection(complement(B), A).is_empty()


def overapprox_set(
    executor,
    EM,
    goal,
    unsafe: StatesSet,
    indtarget,
    assumptions,
    L,
    drop_only: bool = False,
):
    """
    goal - the set to be overapproxiamted
    drop_only - only try to drop clauses, not to extend them
    """
    create_set = executor.create_set
    # unify variables in goal, target, and unsafe
    S = goal.translated(unsafe)
    target = indtarget.translated(unsafe)
    if assumptions:
        assumptions = assumptions.translated(unsafe)

    # assert not S.is_empty(), "Overapproximating empty set"
    assert intersection(
        S, unsafe
    ).is_empty(), f"Whata? Unsafe states among one-step reachable safe states:\nS = {S},\nunsafe = {unsafe}"
    if __debug__:
        # r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
        # assert (
        #    r.errors is None
        # ), f"Input set is not inductive (CTI: {r.errors[0].model()})"
        assert L.set_is_inductive_towards(
            S, target, allow_infeasible_only=True
        ), f"{S} -> {target}"

    dbg(f"Overapproximating {S}", color="dark_blue")
    dbg(f"  with unsafe states: {unsafe}", color="dark_blue")

    expr = S.as_expr()
    if expr.is_concrete():
        return S

    overapprox = LoopStateOverapproximation(S, executor, target, unsafe, L, EM)
    overapprox.drop_clauses(assumptions)

    # NOTE: this works good alone sometimes
    if drop_only:
        S = overapprox.commit()
        return S

    overapprox.overapproximate()

    # drop clauses once more
    overapprox.drop_clauses(None)
    S = overapprox.commit()

    assert intersection(
        unsafe, create_set(S)
    ).is_empty(), "Dropping clauses second time made the set unsafe"

    dbg(f"Overapproximated to {S}", color="orange")

    return S
