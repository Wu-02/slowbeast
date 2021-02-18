from functools import partial
from slowbeast.domains.concrete import ConcreteInt, dom_is_concrete
from slowbeast.util.debugging import dbg
from slowbeast.solvers.expressions import em_optimize_expressions
from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver

from slowbeast.symexe.statesset import union, intersection
from .inductivesequence import InductiveSequence

from slowbeast.core.executor import PathExecutionResult
from .kindsebase import check_paths


from slowbeast.symexe.annotations import (
    AssertAnnotation,
    execute_annotation_substitutions,
)


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
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)
            solver.add(c)

    EM = getGlobalExprManager()
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
        elif changed:
            if len(newc) == 1:
                singletons.append(newc[0])
                solver.add(newc[0])
            else:
                newclauses.append(EM.disjunction(*newc))
        else:
            newclauses.append(r)

    return singletons + newclauses


def postimage(executor, paths, pre=None):
    """
    Return states after executing paths with precondition 'pre'
    extended by the postcondition 'post'. We do not evaluate the
    validity of the postcondition, so that we can get the path condition
    and manipulate with it (it can be unsat and evaluating it could
    simplify it to false, which is undesired here
    """
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if pre:
            p.add_annot_before(pre.as_assume_annotation())

        # FIXME do not branch on last here, its add useless states
        r = executor.executePath(p)
        result.merge(r)

    assert result.errors is None
    if not result.ready:
        return None

    ready = result.ready
    return ready


def literals(c):
    if c.isOr():
        yield from c.children()
    else:
        yield c


def get_predicate(l):
    EM = getGlobalExprManager()
    if l.isSLe():
        return EM.Le
    if l.isSGe():
        return EM.Ge
    if l.isSLt():
        return EM.Lt
    if l.isSGt():
        return EM.Gt
    if l.isULe():
        return partial(EM.Le, unsigned=True)
    if l.isUGe():
        return partial(EM.Ge, unsigned=True)
    if l.isULt():
        return partial(EM.Lt, unsigned=True)
    if l.isUGt():
        return partial(EM.Gt, unsigned=True)

    raise NotImplementedError(f"Unhandled predicate in expr {l}")


def _decompose_literal(l):
    isnot = False
    if l.isNot():
        isnot = True
        l = list(l.children())[0]

    if l.isLt() or l.isLe():
        addtoleft = False
    elif l.isGt() or l.isGe():
        addtoleft = True
    else:
        return None, None, None, None

    chld = list(l.children())
    assert len(chld) == 2
    left, P, right = chld[0], get_predicate(l), chld[1]

    if isnot:
        addtoleft = not addtoleft
        EM = getGlobalExprManager()
        binop = P
        P = lambda a, b: EM.Not(binop(a, b))

    return left, right, P, addtoleft


class DecomposedLiteral:
    __slots__ = "left", "right", "pred", "addtoleft"

    def __init__(self, lit):
        self.left, self.right, self.pred, self.addtoleft = _decompose_literal(lit)

    def __bool__(self):
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
        EM = getGlobalExprManager()
        left, right = self.left, self.right
        if self.addtoleft:
            left = EM.Add(left, num)
        else:
            right = EM.Add(right, num)

        # try pushing further
        return self.pred(left, right)


def get_left_right(l):
    if l.isNot():
        l = list(l.children())[0]

    chld = list(l.children())
    assert len(chld) == 2, "Invalid literal (we assume binop or not(binop)"
    return chld[0], chld[1]


def _check_literal(lit, litrep, I, safety_solver, solver, EM, rl, poststates):
    # safety check
    if not safety_solver.is_sat(EM.disjunction(lit, *rl)) is False:
        return False

    have_feasible = False
    substitute = EM.substitute

    A = AssertAnnotation(substitute(I.expr(), (litrep, lit)), I.substitutions(), EM)
    for s in poststates:
        # feasability check
        solver.push()
        pathcond = substitute(s.path_condition(), (litrep, lit))
        solver.add(pathcond)
        if solver.is_sat() is not True:
            solver.pop()
            continue
        # feasible means ok, but we want at least one feasible path
        # FIXME: do we?
        have_feasible = True

        # inductivity check
        hasnocti = A.do_substitutions(s)
        # we have got pathcond in solver already
        if solver.is_sat(EM.Not(hasnocti)) is not False:  # there exist CTI
            solver.pop()
            return False
        solver.pop()
    return have_feasible


def check_literal(lit, litrep, I, safety_solver, solver, EM, rl, poststates):
    if lit is None or lit.is_concrete():
        return False
    return _check_literal(lit, litrep, I, safety_solver, solver, EM, rl, poststates)


def extend_with_num(
    dliteral,
    litrep,
    constadd,
    num,
    maxnum,
    I,
    safety_solver,
    solver,
    EM,
    rl,
    poststates,
):
    """
    Add 'num' to the literal 'l' as many times as is possible

    dliteral, litrep - literal FIXME: merge into one?
    constadd - this number is always added to the literal (that is the current
               value of extending
    num - number to keep adding
    maxnum - maximal number to try (the sum of added 'num' cannot exceed this)

    \return the maximal added number which is multiple of 'num' + constadd,
            i.e., the new value that is safe to add to the literal
    """
    numval = num.value()
    retval = constadd
    Add = EM.Add

    # keep the retval also in python int, so that we can check it agains
    # maxnum (expressions are counted modulo, so we cannot check that
    # on expressions)
    acc = retval.value() + numval
    if acc > maxnum:
        return retval

    newretval = Add(retval, num)
    newl = dliteral.extended(newretval)

    ### push as far as we can with this num
    while check_literal(newl, litrep, I, safety_solver, solver, EM, rl, poststates):
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


def extend_literal(
    goodl, dliteral: DecomposedLiteral, litrep, I, safety_solver, solver, rl, poststates
):

    bw = dliteral.bitwidth()
    two = ConcreteInt(2, bw)
    # adding 2 ** bw would be like adding 0, stop before that
    maxnum = 2 ** bw - 1

    EM = getGlobalExprManager()

    # a fast path where we try shift just by one.  If we cant, we can give up
    # FIXME: try more low values (e.g., to 10)
    num = ConcreteInt(1, bw)
    l = dliteral.extended(num)
    if not check_literal(l, litrep, I, safety_solver, solver, EM, rl, poststates):
        return goodl

    # this is the final number that we are going to add to one side of the
    # literal
    finalnum = ConcreteInt(1, bw)  # we know we can add 1 now
    num = ConcreteInt(2 ** (bw - 1) - 1, bw)  # this num we'll try to add
    while finalnum.value() <= maxnum:
        finalnum = extend_with_num(
            dliteral,
            litrep,
            finalnum,
            num,
            maxnum,
            I,
            safety_solver,
            solver,
            EM,
            rl,
            poststates,
        )

        if num.value() <= 1:
            # we have added also as many 1 as we could, finish
            return dliteral.extended(finalnum)
        num = EM.Div(num, two)
    raise RuntimeError("Unreachable")


def overapprox_literal(l, rl, S, unsafe, target, executor, L):
    """
    l - literal
    rl - list of all literals in the clause
    S - rest of clauses of the formula except for 'rl'
    unsafe - set of unsafe states
    target - set of safe states that we want to keep reachable
    """
    assert not l.isAnd() and not l.isOr(), f"Input is not a literal: {l}"
    assert intersection(S, l, unsafe).is_empty(), "Unsafe states in input"
    goodl = l  # last good overapprox of l

    dliteral = DecomposedLiteral(l)
    if not dliteral:
        return goodl

    assert dliteral.toformula() == goodl
    EM = getGlobalExprManager()
    disjunction = EM.disjunction

    # create a fresh literal that we use as a symbol for our literal during extending
    litrep = EM.Bool("litext")
    # X is the original formula with 'litrep' instead of 'l'
    X = intersection(S, disjunction(litrep, *(x for x in rl if x != l)))
    assert not X.is_empty(), f"S: {S}, l: {l}, rl: {rl}"
    post = postimage(executor, L.paths(), pre=X)
    if not post:
        return goodl
    # U is allowed reachable set of states
    U = union(target, X)
    I = U.as_assume_annotation()
    # execute the instructions from annotations, so that the substitutions have up-to-date value
    poststates, nonr = execute_annotation_substitutions(
        executor.ind_executor(), post, I
    )
    assert not nonr, f"Got errors while processing annotations: {nonr}"

    # we always check S && unsafe && new_clause, so we can keep S  and unsafe
    # in the solver all the time
    safety_solver = IncrementalSolver()
    safety_solver.add(S.as_expr())
    safety_solver.add(unsafe.as_expr())

    solver = IncrementalSolver()

    em_optimize_expressions(False)
    # the optimizer could make And or Or from the literal, we do not want that...
    goodl = extend_literal(
        goodl, dliteral, litrep, I, safety_solver, solver, rl, poststates
    )
    em_optimize_expressions(True)

    return goodl


def overapprox_clause(c, R, executor, L, unsafe, target):
    """c - the clause
    R - rest of clauses of the formula
    unsafe - unsafe states
    target - safe states that should be reachable from c \cap R
    """
    EM = R.get_se_state().expr_manager()

    assert intersection(R, c, unsafe).is_empty(), f"{R} \cap {c} \cap {unsafe}"
    if __debug__:
        X = R.copy()
        X.intersect(c)
        r = check_paths(executor, L.paths(), pre=X, post=union(X, target))
        assert (
            r.errors is None
        ), f"Input state is not inductive (CTI: {r.errors[0].model()})"

    newc = []
    lits = list(literals(c))
    simplify = EM.simplify

    for l in lits:
        newl = simplify(overapprox_literal(l, lits, R, unsafe, target, executor, L))
        newc.append(newl)
        dbg(
            f"  Overapproximated {l} --> {newl}",
            color="gray",
        )

        if __debug__:
            X = R.copy()
            X.intersect(
                EM.disjunction(
                    *(newc[i] if i < len(newc) else lits[i] for i in range(len(lits)))
                )
            )
            r = check_paths(executor, L.paths(), pre=X, post=union(X, target))
            if r.errors:
                print("States:", X)
                print("Target:", target)
                print(r.errors[0].path_condition())
            assert (
                r.errors is None
            ), f"Extended literal renders state non-inductive (CTI: {r.errors[0].model()})"

    if len(newc) == 1:
        return newc[0]

    return EM.disjunction(*newc)


def break_const_eq(expr):
    EM = getGlobalExprManager()
    clauses = []

    def break_eq(c):
        l, r = c.children()
        ret = []
        if dom_is_concrete(l) or dom_is_concrete(r):
            for x in  EM.Le(l, r), EM.Le(r, l):
                if not x.is_concrete():
                    ret.append(x)
            return ret

        return [c]

    # break equalities that have a constant on one side,
    # so that we can generalize them
    for c in expr.children():
        if c.isEq():
            clauses.extend(break_eq(c))
        else:
            clauses.append(c)

    return clauses


def drop_clauses(clauses, S, target, EM, L, safesolver, executor):
    # we start with all clauses
    newclauses = clauses.copy()
    conjunction = EM.conjunction
    lpaths = L.paths()
    for c in clauses:
        assert not c.is_concrete(), c
        # create a temporary formula without the given clause
        tmp = newclauses.copy()
        tmp.remove(c)

        # check whether we can get rid of the clause
        tmpexpr = conjunction(*tmp)
        if tmpexpr.is_concrete():
            continue  # either False or True are bad for us
        if safesolver.is_sat(tmpexpr) is not False:
            continue  # unsafe overapprox
        X = S.copy()
        X.reset_expr(tmpexpr)
        r = check_paths(executor, lpaths, pre=X, post=union(X, target))
        for s in r.killed():
            dbg("Killed a state")
            return newclauses
        if r.errors is None and r.ready:
            newclauses = tmp
            dbg(f"  dropped {c}...")

    return newclauses


def drop_clauses_fixpoint(clauses, S, target, EM, L, safesolver, executor):
    """ Drop clauses until fixpoint """
    newclauses = clauses
    while True:
        oldlen = len(newclauses)
        newclauses = drop_clauses(newclauses, S, target, EM, L, safesolver, executor)
        if oldlen == len(newclauses):
            break
    return newclauses


def enumerate_clauses(clauses, create_set):
    """ Return pair (clause, rest of clauses (as set) """
    tmp = create_set()
    for n in range(len(clauses)):
        tmp = create_set()
        c = None
        for i, x in enumerate(clauses):
            if i == n:
                c = x
            else:
                tmp.intersect(x)
        assert c
        yield c, tmp


def overapprox_set(executor, EM, S, unsafeAnnot, target, L, drop_only=False):
    """
    drop_only - only drop redundant clauses
    """
    create_set = executor.ind_executor().create_states_set
    unsafe = create_set(unsafeAnnot)  # safe strengthening
    assert not S.is_empty(), "Overapproximating empty set"
    assert intersection(
        S, unsafe
    ).is_empty(), f"Whata? Unsafe states among one-step reachable safe states:\nS = {S},\nunsafe = {unsafe}"
    if __debug__:
        r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
        assert (
            r.errors is None
        ), f"Input set is not inductive (CTI: {r.errors[0].model()})"

    dbg(f"Overapproximating {S}", color="dark_blue")
    dbg(f"  with unsafe states: {unsafe}", color="dark_blue")

    expr = S.as_expr()
    if expr.is_concrete():
        return InductiveSequence.Frame(S.as_assert_annotation(), None)

    expr = expr.to_cnf()
    # break equalities with constants to <= && >= so that we can overapproximate them
    clauses = break_const_eq(expr)
    # clauses = list(expr.children())

    safesolver = IncrementalSolver()
    safesolver.add(unsafe.as_expr())

    # can we drop some clause completely?
    newclauses = drop_clauses_fixpoint(clauses, S, target, EM, L, safesolver, executor)
    clauses = remove_implied_literals(newclauses)

    # FIXME: THIS WORKS GOOD!
    if drop_only:
        S.reset_expr(EM.conjunction(*clauses))
        return InductiveSequence.Frame(S.as_assert_annotation(), None)

    # Now take every clause c and try to overapproximate it
    newclauses = []
    for c, xc in enumerate_clauses(clauses, create_set):
        # R is the rest of the formula without the clause c
        R = S.copy()  # copy the substitutions
        R.reset_expr(xc.as_expr())

        newclause = overapprox_clause(c, R, executor, L, unsafe, target)
        if newclause:
            # newclauses.append(newclause)
            # FIXME: this check should be assertion,
            # overapprox_clause should not give us such clauses
            tmp = R.copy()
            tmp.intersect(newclause)
            tmp.complement()
            # assert intersection(tmp, S).is_empty()
            if intersection(tmp, S).is_empty():
                newclauses.append(newclause)
            else:
                newclauses.append(c)
        else:
            newclauses.append(c)

    # drop clauses once more
    # newclauses = drop_clauses_fixpoint(newclauses, S, target, EM, L,
    #                                   safesolver, executor)
    clauses = remove_implied_literals(newclauses)
    S.reset_expr(EM.conjunction(*clauses))

    dbg(f"Overapproximated to {S}", color="dark_blue")

    return InductiveSequence.Frame(S.as_assert_annotation(), None)
