from functools import partial
from slowbeast.domains.concrete import ConcreteInt, dom_is_concrete
from slowbeast.util.debugging import dbg, dbgv
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


def check_literal(EM, lit, ldata):
    if lit is None or lit.is_concrete():
        return False

    # safety check
    if not ldata.safety_solver.is_sat(EM.disjunction(lit, *ldata.clause)) is False:
        return False

    have_feasible = False
    substitute = EM.substitute

    I = ldata.indset_with_placeholder
    placeholder = ldata.placeholder
    solver = ldata.solver
    A = AssertAnnotation(
        substitute(I.expr(), (placeholder, lit)), I.substitutions(), EM
    )
    for s in ldata.loop_poststates:
        # feasability check
        solver.push()
        pathcond = substitute(s.path_condition(), (placeholder, lit))
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


def extend_with_num(dliteral, constadd, num, maxnum, ldata, EM):
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
    while check_literal(EM, newl, ldata):
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


def extend_literal(ldata, EM):
    dliteral = ldata.decomposed_literal

    bw = dliteral.bitwidth()
    two = ConcreteInt(2, bw)
    # adding 2 ** bw would be like adding 0, stop before that
    maxnum = 2 ** bw - 1

    # a fast path where we try shift just by one.  If we cant, we can give up
    # FIXME: try more low values (e.g., to 10)
    num = ConcreteInt(1, bw)
    l = dliteral.extended(num)
    if not check_literal(EM, l, ldata):
        return ldata.literal

    # this is the final number that we are going to add to one side of the
    # literal
    finalnum = ConcreteInt(1, bw)  # we know we can add 1 now
    num = ConcreteInt(2 ** (bw - 1) - 1, bw)  # this num we'll try to add
    while finalnum.value() <= maxnum:
        finalnum = extend_with_num(dliteral, finalnum, num, maxnum, ldata, EM)

        if num.value() <= 1:
            # we have added also as many 1 as we could, finish
            return dliteral.extended(finalnum)
        num = EM.Div(num, two)
    raise RuntimeError("Unreachable")


class OverapproximationData:
    """
    Structure holding information needed for over-approximations
    """

    __slots__ = "executor", "target", "unsafe", "loop", "expr_mgr"

    def __init__(self, executor, target, unsafe, loop, expr_mgr):
        self.executor = executor
        self.target = target
        self.unsafe = unsafe
        self.loop = loop
        self.expr_mgr = expr_mgr


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
        safety_solver,
        solver,
        loop_poststates,
    ):
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


def overapprox_literal(l, rl, S, data):
    """
    l - literal
    rl - list of all literals in the clause
    S - rest of clauses of the formula except for 'rl'
    unsafe - set of unsafe states
    target - set of safe states that we want to keep reachable
    """
    assert not l.isAnd() and not l.isOr(), f"Input is not a literal: {l}"
    assert intersection(S, l, data.unsafe).is_empty(), "Unsafe states in input"

    dliteral = DecomposedLiteral(l)
    if not dliteral:
        return l

    assert dliteral.toformula() == l
    EM = data.expr_mgr
    executor = data.executor

    # create a fresh literal that we use as a placeholder instead of our literal during extending
    placeholder = EM.Bool("litext")
    # X is the original formula with 'placeholder' instead of 'l'
    clause_without_lit = list(x for x in rl if x != l)
    X = intersection(S, EM.disjunction(placeholder, *clause_without_lit))
    assert not X.is_empty(), f"S: {S}, l: {l}, rl: {rl}"
    post = postimage(executor, data.loop.paths(), pre=X)
    if not post:
        return l
    # U is allowed reachable set of states
    U = union(data.target, X)
    indset_with_placeholder = U.as_assume_annotation()
    # execute the instructions from annotations, so that the substitutions have up-to-date value
    poststates_with_placeholder, nonr = execute_annotation_substitutions(
        executor.ind_executor(), post, indset_with_placeholder
    )
    assert not nonr, f"Got errors while processing annotations: {nonr}"

    # we always check S && unsafe && new_clause, so we can keep S  and unsafe
    # in the solver all the time
    safety_solver = IncrementalSolver()
    safety_solver.add(S.as_expr())
    safety_solver.add(data.unsafe.as_expr())

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
    # the optimizer could make And or Or from the literal, we do not want that...
    l = extend_literal(ldata, EM)
    em_optimize_expressions(True)

    return l


def overapprox_clause(c, R, data):
    """c - the clause
    R - rest of clauses of the formula
    unsafe - unsafe states
    target - safe states that should be reachable from c \cap R
    """
    EM = data.expr_mgr

    assert intersection(
        R, c, data.unsafe
    ).is_empty(), f"{R} \cap {c} \cap {data.unsafe}"
    if __debug__:
        X = R.copy()
        X.intersect(c)
        r = check_paths(
            data.executor, data.loop.paths(), pre=X, post=union(X, data.target)
        )
        assert (
            r.errors is None
        ), f"Input state is not inductive (CTI: {r.errors[0].model()})"

    newc = []
    lits = list(literals(c))
    simplify = EM.simplify

    for l in lits:
        newl = simplify(overapprox_literal(l, lits, R, data))
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
            r = check_paths(
                data.executor, data.loop.paths(), pre=X, post=union(X, data.target)
            )
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


def break_eqs(expr):
    EM = getGlobalExprManager()
    clauses = []

    def break_eq(c):
        l, r = c.children()
        ret = []
        # if not const_only or (dom_is_concrete(l) or dom_is_concrete(r)):
        for x in EM.Le(l, r), EM.Le(r, l):
            if not x.is_concrete():
                ret.append(x)
        return ret
        # return [c]

    # break equalities that have a constant on one side,
    # so that we can generalize them
    for c in expr.children():
        if c.isEq():
            clauses.extend(break_eq(c))
        else:
            clauses.append(c)

    return clauses

def replace_constants(expr, EM):
    "Assume the expr is in CNF"
    added = []
    # FIXME: this is veeery inefficient
    muls = [c for c in expr.subexpressions() if not c.is_concrete() and c.isMul()]
    for m in muls:
        chld = list(m.children())
        if chld[0].is_concrete():
            r = EM.fresh_value("const_repl", chld[0].type())
            added.append(EM.Eq(r, chld[0]))
            expr = EM.substitute(expr, (m, EM.Mul(r, chld[1])))
        if chld[1].is_concrete():
            r = EM.fresh_value("const_repl", chld[1].type())
            added.append(EM.Eq(r, chld[1]))
            expr = EM.substitute(expr, (m, EM.Mul(chld[0], r)))

    return EM.conjunction(expr, *added)

def _get_pre_post_states(executor, paths):
    """
    Return states from before and after executing paths.
    These states can be used to get pre/post conditions of the path
    using Annotations (do_substitutions()) and then checking along
    with that path_condition.
    """
    r = check_paths(executor, paths)
    for s in r.killed():
        dbg("Killed a state")
        return None, None
    return executor.ind_executor().createCleanState(), r.ready


def drop_clauses(clauses, S, safesolver, data, nodrop_safe=True, no_vars_eq=False):
    "no_vars_eq: do not drop equalities between variables"
    target, executor = data.target, data.executor

    # we start with all clauses
    conjunction = data.expr_mgr.conjunction
    lpaths = data.loop.paths()
    expressions_with_constants = set()
    expressions = set()
    vars_eq = set()
    for c in clauses:
        if c.is_concrete():
            if c.value() is False:
                dbg("  ... got FALSE in clauses, returning FALSE")
                return [data.expr_mgr.getFalse()]
            else:
                dbg("  ... dropping True clause")
        else:
            d = next(c.children()) if c.isNot() else c
            has_concr = any(map(lambda x: x.is_concrete(), d.children()))

            if c.isEq() and not has_concr:
                vars_eq.add(c)
            else:
                (expressions_with_constants if has_concr else expressions).add(c)

    # droping clauses with constants has priority over dopping those
    # without constants
    clauses = list(expressions_with_constants)
    clauses.extend(expressions)
    if not no_vars_eq:
        clauses.extend(vars_eq)
    newclauses = clauses.copy()
    for c in clauses:
        if nodrop_safe and safesolver.is_sat(c) is False:
            # do not drop clauses that refute the error states,
            # those may be useful
            continue

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
    if no_vars_eq:
        newclauses.extend(vars_eq)

    return newclauses


def drop_clauses_fixpoint(clauses, S, safesolver, data, nodrop_safe=True, no_vars_eq=False):
    """ Drop clauses until fixpoint """
    newclauses = clauses
    while True:
        dbgv(" ... droping clauses (starting iteration)")
        oldlen = len(newclauses)
        newclauses = drop_clauses(newclauses, S, safesolver, data, nodrop_safe, no_vars_eq)
        if oldlen == len(newclauses):
            break
    dbgv(" ... done droping clauses")
    return newclauses


def overapprox_set(executor, EM, S, unsafeAnnot, target, L, drop_only=False):
    """
    drop_only - only try to drop clauses, not to extend them
    """
    create_set = executor.create_set
    unsafe = create_set(unsafeAnnot)
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

    data = OverapproximationData(executor, target, unsafe, L, EM)

    expr = S.as_expr()
    if expr.is_concrete():
        return InductiveSequence.Frame(S.as_assert_annotation(), None)

    expr = expr.to_cnf()
    # break equalities to <= && >= so that we can overapproximate them
    #expr = replace_constants(expr, EM)
    clauses = break_eqs(expr)

    assert intersection(
        unsafe, create_set(EM.conjunction(*clauses))
    ).is_empty(), f"Simplifying and enriching the formula made it unsafe"


    safesolver = IncrementalSolver()
    safesolver.add(unsafe.as_expr())

    # can we drop some clause True?
    newclauses = drop_clauses_fixpoint(clauses, S, safesolver, data, nodrop_safe=True, no_vars_eq=True)
    clauses = remove_implied_literals(newclauses)

    assert intersection(
        unsafe, create_set(EM.conjunction(*clauses))
    ).is_empty(), f"Dropping clauses made the set unsafe"

    # FIXME: THIS WORKS GOOD!
    if drop_only:
        # newclauses = drop_clauses_fixpoint(clauses, S, safesolver, data)
        # clauses = remove_implied_literals(newclauses)
        S.reset_expr(EM.conjunction(*clauses))
        return InductiveSequence.Frame(S.as_assert_annotation(), None)

    # Now take every clause c and try to overapproximate it
    conjunction = EM.conjunction
    newclauses = []
    for n in range(len(clauses)):
        assert len(newclauses) == n
        c = clauses[n]
        # R is the rest of the actual formula without the clause c
        R = S.copy()  # copy the substitutions
        R.reset_expr(conjunction(*newclauses, *clauses[n + 1 :]))

        newclause = overapprox_clause(c, R, data)
        if newclause:
            # newclauses.append(newclause)
            # FIXME: this check should be
            # assertion, overapprox_clause should not give us such clauses
            tmp = R.copy()
            tmp.intersect(newclause)
            assert intersection(
                tmp, unsafe
            ).is_empty(), f"Overapprox clause: got unsafe set {c} --> {newclause}"
            tmp.complement()
            # assert intersection(tmp, S).is_empty()
            if intersection(tmp, S).is_empty():
                # new clause makes S to be an overapproximation, good
                newclauses.append(newclause)
            else:
                newclauses.append(c)
        else:
            newclauses.append(c)

        if __debug__:
            R.intersect(newclauses[-1])
            assert not R.is_empty()
            R.intersect(unsafe)
            assert R.is_empty(), f"Overapproxmating clause made the set unsafe: {c}"

    if __debug__:
        S.reset_expr(EM.conjunction(*newclauses))
        assert not S.is_empty()
        assert intersection(
            unsafe, S
        ).is_empty(), f"Overapproxmating clauses made the set unsafe"

    # drop clauses once more
    newclauses = drop_clauses_fixpoint(newclauses, S, safesolver, data)

    clauses = remove_implied_literals(newclauses)
    S.reset_expr(EM.conjunction(*clauses))

    assert intersection(
        unsafe, create_set(S)
    ).is_empty(), f"Dropping clauses second time made the set unsafe"

    dbg(f"Overapproximated to {S}", color="dark_blue")

    return S
