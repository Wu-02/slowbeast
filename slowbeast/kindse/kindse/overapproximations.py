from functools import partial
from slowbeast.domains.concrete import ConcreteInt
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
            p.addPrecondition(pre.as_assume_annotation())

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
        self.left, self.right,  self.pred, self.addtoleft = _decompose_literal(lit)

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

    def extend(self, num):
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
    for s in poststates:
        # feasability check
        solver.push()
        pathcond = EM.substitute(s.path_condition(), (litrep, lit))
        solver.add(pathcond)
        if solver.is_sat() is not True:
            solver.pop()
            continue
        # feasible means ok, but we want at least one feasible path
        # FIXME: do we?
        have_feasible = True

        # inductivity check
        A = AssertAnnotation(
            EM.substitute(I.getExpr(), (litrep, lit)), I.getSubstitutions(), EM
        )
        hasnocti = A.doSubs(s)
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

def extend_literal(goodl, dliteral : DecomposedLiteral, litrep, I, safety_solver, solver, rl, poststates):
    bw = dliteral.bitwidth()
    two = ConcreteInt(2, bw)
    maxnum = 2 ** bw - 1 # adding 2 ** bw - 1 would be like adding 0

    EM = getGlobalExprManager()

    # check if we can drop the literal completely
    # XXX: is this any good? We already dropped the literals...
    if _check_literal(EM.getTrue(), litrep, I, safety_solver, solver, EM, rl, poststates):
        return EM.getTrue()

    # a fast path where we try shift just by one.
    # If we cant, we can give up
    # FIXME: try more low values (e.g., to 10)
    num = ConcreteInt(1, bw)
    l = dliteral.extend(num)
    if not check_literal(l, litrep, I, safety_solver, solver, EM, rl, poststates):
        return goodl

    resultnum = ConcreteInt(1, bw)
    Add = EM.Add
    num = ConcreteInt(2 ** (bw - 1) - 1, bw)
    while resultnum.value() <= maxnum:
        numval = num.value()
        # do not try to shift the number by more than 2^bw
        nextval = Add(resultnum, num)
        l = dliteral.extend(nextval)

        # push as far as we can with this num
        while check_literal(l, litrep, I, safety_solver, solver, EM, rl, poststates):
            assert resultnum.value() <= maxnum
            resultnum = nextval
            nextval = Add(resultnum, num)

            if nextval.value() > maxnum:
                break
            l = dliteral.extend(nextval)

        if numval <= 1:
            # we have added also as many 1 as we could, finish
            return dliteral.extend(resultnum)
        num = EM.Div(num, two)


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
    X = intersection(S, disjunction(litrep, *rl))
    assert not X.is_empty()
    post = postimage(executor, L.getPaths(), pre=X)
    if not post:
        return goodl
    # U is allowed reachable set of states
    U = union(target, X)
    I = U.as_assume_annotation()
    # execute the instructions from annotations, so that the substitutions have up-to-date value
    poststates, nonr = execute_annotation_substitutions(
        executor.getIndExecutor(), post, I
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
    goodl = extend_literal(goodl, dliteral, litrep, I, safety_solver, solver, rl, poststates)
    em_optimize_expressions(True)

    return goodl


#
# def split_nth_item(items, n):
#     item = None
#     rest = []
#     for i, x in enumerate(items):
#         if i == n:
#             item = x
#         else:
#             rest.append(x)
#     return item, rest


def overapprox_clause(c, S, executor, L, unsafe, target):
    assert intersection(S, c, unsafe).is_empty(), f"{S} \cap {c} \cap {unsafe}"

    newc = []
    lits = list(literals(c))
    for l in lits:
        newl = overapprox_literal(l, lits, S, unsafe, target, executor, L)
        newc.append(newl)
        dbg(
            f"  Overapproximated {l} ==> {getGlobalExprManager().simplify(newl)}",
            color="gray",
        )

    if len(newc) == 1:
        return newc[0]

    EM = S.get_se_state().getExprManager()
    return EM.disjunction(*newc)


def break_eq_ne(expr):
    EM = getGlobalExprManager()
    clauses = []
    # break equalities and inequalities, so that we can generalize them
    for c in expr.children():
        if c.isEq():
            l, r = c.children()
            clauses.append(EM.Le(l, r))
            clauses.append(EM.Le(r, l))
        elif c.isNot():
            (d,) = c.children()
            if d.isEq():
                l, r = d.children()
                clauses.append(EM.Lt(l, r))
                clauses.append(EM.Gt(l, r))
            else:
                clauses.append(c)
        else:
            clauses.append(c)

    return clauses



def overapprox_set(executor, EM, S, unsafeAnnot, seq, L):
    createSet = executor.getIndExecutor().createStatesSet
    unsafe = createSet(unsafeAnnot)  # safe strengthening
    assert intersection(
        S, unsafe
    ).is_empty(), f"Whata? Unsafe states among one-step reachable safe states:\nS = {S},\nunsafe = {unsafe}"

    dbg(f"Overapproximating {S}", color="dark_blue")
    dbg(f"  with unsafe states: {unsafe}", color="dark_blue")
    # FIXME: move target one level up
    target = createSet(seq[-1].toassert())

    expr = S.as_expr()
    if expr.is_concrete():
        return InductiveSequence.Frame(S.as_assert_annotation(), None)

    expr = expr.to_cnf()
    # clauses = break_eq_ne(expr)
    clauses = list(expr.children())

    safesolver = IncrementalSolver()
    safesolver.add(unsafe.as_expr())

    # can we drop a clause completely?
    newclauses = clauses.copy()
    for c in clauses:
        tmp = newclauses.copy()
        tmp.remove(c)

        tmpexpr = EM.conjunction(*tmp)
        if tmpexpr.is_concrete():
            continue  # either False or True are bad for us
        if safesolver.is_sat(tmpexpr) is not False:
            continue  # unsafe overapprox
        X = S.copy()
        X.reset_expr(tmpexpr)
        r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
        if r.errors is None and r.ready:
            newclauses = tmp
            # dbg(f"  dropped {c}...")

    clauses = remove_implied_literals(newclauses)
    newclauses = []

    for n in range(0, len(clauses)):
        tmp = createSet()
        c = None
        for i, x in enumerate(clauses):
            if i == n:
                c = x
            else:
                tmp.intersect(x)
        assert c
        R = S.copy()
        R.reset_expr(tmp.as_expr())
        newclause = overapprox_clause(c, R, executor, L, unsafe, target)
        if newclause:
            newclauses.append(newclause)

    clauses = remove_implied_literals(newclauses)
    S.reset_expr(EM.conjunction(*clauses))

    # FIXME: drop clauses once more?

    dbg(f"Overapproximated to {S}", color="dark_blue")

    sd = S.as_description()
    A1 = AssertAnnotation(sd.getExpr(), sd.getSubstitutions(), EM)
    return InductiveSequence.Frame(S.as_assert_annotation(), None)
