from functools import partial

from slowbeast.domains.concrete import ConcreteInt
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.core.executor import PathExecutionResult
from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    or_annotations,
    execute_annotation_substitutions,
)

from slowbeast.symexe.statesset import union, intersection
from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver
from slowbeast.solvers.expressions import em_optimize_expressions

from .loops import SimpleLoop
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence


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


def get_initial_seq2(unsafe, path, L):
    """
    Return two annotations, one that is the initial safe sequence
    and one that represents the error states
    """
    # NOTE: Only safe states that reach the assert are not inductive on the
    # loop header -- what we need is to have safe states that already left
    # the loop and safely pass assertion or avoid it.
    # These are the complement of error states intersected with the
    # negation of loop condition.

    S = None  # safe states
    E = None  # unsafe states

    EM = getGlobalExprManager()
    Or, conjunction = EM.Or, EM.conjunction
    for u in unsafe:
        uconstr = u.getConstraints()
        E = Or(conjunction(*uconstr), E) if E else conjunction(*uconstr)

    S = EM.Not(E)

    # simplify the formulas
    if not S.is_concrete():
        S = conjunction(*remove_implied_literals(S.to_cnf().children()))
    if not E.is_concrete():
        E = conjunction(*remove_implied_literals(E.to_cnf().children()))

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, None), InductiveSequence.Frame(Se, None)


def get_initial_seq(unsafe, path, L):
    """
    Return two annotations, one that is the initial safe sequence
    and one that represents the error states.
    This implementation returns not the weakest sets, but stronger sets
    that should be easier to prove (and then we can prove the remaining
    states safe in another iteration).
    """

    # NOTE: Only safe states that reach the assert are not inductive on the
    # loop header -- what we need is to have safe states that already left
    # the loop and safely pass assertion or avoid it.
    # These are the complement of error states intersected with the
    # negation of loop condition.

    S = None  # safe states
    E = None  # unsafe states

    EM = getGlobalExprManager()
    Not, conjunction = EM.Not, EM.conjunction
    for u in unsafe:
        # add constraints without loop exit condition
        # (we'll add the loop condition later)
        uconstr = u.getConstraints()
        if not uconstr:
            S = EM.getFalse()
            E = EM.getTrue()
            break  # nothing we can do...
        # all constr. apart from the last one
        pc = conjunction(*uconstr[:-1])
        # last constraint is the failed assertion
        S = conjunction(pc, Not(uconstr[-1]), S) if S else EM.And(pc, Not(uconstr[-1]))
        # unsafe states
        E = EM.Or(conjunction(*uconstr), E) if E else conjunction(*uconstr)

    # simplify the formulas
    if not S.is_concrete():
        S = conjunction(*remove_implied_literals(S.to_cnf().children()))
    if not E.is_concrete():
        E = conjunction(*remove_implied_literals(E.to_cnf().children()))

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, None), InductiveSequence.Frame(Se, None)


def check_paths(executor, paths, pre=None, post=None):
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.addPostcondition(post.as_assert_annotation())

        if pre:
            p.addPrecondition(pre.as_assume_annotation())

        r = executor.executePath(p)
        result.merge(r)

    return result


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


def decompose_literal(l):
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


def get_left_right(l):
    if l.isNot():
        l = list(l.children())[0]

    chld = list(l.children())
    assert len(chld) == 2, "Invalid literal (we assume binop or not(binop)"
    return chld[0], chld[1]


def overapprox_literal(l, rl, S, unsafe, target, executor, L):
    assert not l.isAnd() and not l.isOr(), f"Input is not a literal: {l}"
    assert intersection(S, l, unsafe).is_empty(), "Unsafe states in input"
    goodl = l  # last good overapprox of l

    left, right, P, addtoleft = decompose_literal(l)
    if left is None:
        assert right is None
        return goodl

    EM = getGlobalExprManager()
    disjunction = EM.disjunction

    # create a fresh literal that we use as a symbol for our literal during extending
    litrep = EM.Bool("litext")
    X = intersection(S, disjunction(litrep, *rl))
    assert not X.is_empty()
    post = postimage(executor, L.getPaths(), pre=X)
    if not post:
        return goodl
    formulas = []
    U = union(target, X)
    I = U.as_assume_annotation()
    step = I.getExpr()
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

    def _check_literal(lit):
        # safety check
        if not safety_solver.is_sat(disjunction(lit, *rl)) is False:
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

    def check_literal(lit):
        if lit.is_concrete():
            return False
        return _check_literal(lit)

    #
    # # NOTE: the check above should be equivalent to this code but should be faster as we do not re-execute
    # # the paths all the time
    # def check_literal_old(lit):
    #     if lit.is_concrete():
    #         return False
    #     X = intersection(S, disjunction(lit, *rl))
    #     if not intersection(X, unsafe).is_empty():
    #         return False
    #
    #     r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
    #     return r.errors is None and r.ready is not None
    #
    # def check_literal(lit):
    #     r = check_literal_new(lit)
    #     assert r == check_literal_old(lit), f"{lit} : {r}"
    #     return r

    def modify_literal(goodl, P, num):
        assert (
            not goodl.isAnd() and not goodl.isOr()
        ), f"Input is not a literal: {goodl}"
        # FIXME: wbt. overflow?
        left, right = get_left_right(goodl)
        if addtoleft:
            left = EM.Add(left, num)
        else:
            right = EM.Add(right, num)

        # try pushing further
        l = P(left, right)
        if l.is_concrete():
            return None
        if l == goodl:  # got nothing new...
            return None
        return l

    # FIXME: add a fast path where we try several values from the bottom...

    def extend_literal(goodl):
        bw = left.type().bitwidth()
        two = ConcreteInt(2, bw)
        maxnum = 2 ** bw - 1
        accnum = 1

        # check if we can drop the literal completely
        if _check_literal(EM.getTrue()):
            return EM.getTrue()

        # a fast path where we try shift just by one.
        # If we cant, we can give up
        num = ConcreteInt(1, bw)
        l = modify_literal(goodl, P, num)
        if l is None:
            return goodl

        if check_literal(l):
            goodl = l
        else:
            return goodl

        # FIXME: try more low values (e.g., to 10)

        # generic case
        num = ConcreteInt(2 ** (bw - 1) - 1, bw)

        while True:
            numval = num.value()
            # do not try to shift the number by more than 2^bw
            if accnum + numval > maxnum:
                return goodl

            accnum += numval
            l = modify_literal(goodl, P, num)
            if l is None:
                return goodl

            # push as far as we can with this num
            while check_literal(l):
                assert accnum <= maxnum
                goodl = l

                if accnum + numval > maxnum:
                    break

                accnum += numval
                l = modify_literal(goodl, P, num)
                if l is None:
                    break

            if numval <= 1:
                return goodl
            num = EM.Div(num, two)

    em_optimize_expressions(False)
    # the optimizer could make And or Or from the literal, we do not want that...
    goodl = extend_literal(goodl)
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

    createSet = executor.getIndExecutor().createStatesSet

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


def overapprox(executor, s, unsafeAnnot, seq, L):
    S = executor.getIndExecutor().createStatesSet(s)
    EM = s.getExprManager()
    return overapprox_set(executor, EM, S, unsafeAnnot, seq, L)


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


def join_iter(i1, i2):
    yield from i1
    yield from i2


def simplify_expr(expr, EM):
    return EM.conjunction(*remove_implied_literals(expr.to_cnf().children()))


class KindSymbolicExecutor(BaseKindSE):
    def __init__(self, prog, ohandler=None, opts=KindSeOptions(), programstructure=None):
        super().__init__(
            prog=prog, ohandler=ohandler, opts=opts, programstructure=programstructure
        )

        self.readypaths = []
        self.stalepaths = []

        self.invpoints = {}

        self.genannot = False
        self.sum_loops = {}

    def handle_loop(self, loc, path, states):
        assert (
            loc in self.sum_loops[loc.getCFG()]
        ), "Handling a loop that should not be handled"

        # first try to unroll it in the case the loop
        # is easy to verify
        kindse = BaseKindSE(self.getProgram())
        maxk = 15
        dbg_sec("Running nested KindSE")
        res = kindse.run([path.copy()], maxk=maxk)
        dbg_sec()
        if res == 0:
            print_stdout(
                f"Loop {loc.getBBlockID()} proved by the basic KindSE", color="GREEN"
            )
            return True

        if not self.execute_loop(path, loc, states):
            self.sum_loops[loc.getCFG()].remove(loc)
            print_stdout(
                f"Falling back to unwinding loop {loc.getBBlockID()}", color="BROWN"
            )
            return False
        return True

    def extend_seq(self, seq, errs0, L):
        S = self.getIndExecutor().createStatesSet(seq[-1].toassert())
        r = check_paths(self, L.getPaths(), post=S)
        if not r.ready:  # cannot step into this frame...
            # FIXME we can use it at least for annotations
            dbg("Infeasible frame...")
            return []

        EM = getGlobalExprManager()
        E = []

        for s in r.ready:
            e = overapprox(self, s, errs0.toassert(), seq, L)
            if e == seq[-1]:
                dbg("Did not extend with the same elem...")
                continue
            print_stdout(f"Extended with: {e}", color="BROWN")
            tmp = seq.copy()
            tmp.append(e.states, e.strengthening)

            if __debug__:
                r = tmp.check_ind_on_paths(self, L.getPaths())
                assert (
                    r.errors is None
                ), f"Extended sequence is not inductive (CTI: {r.errors[0].model()})"

            E.append(tmp)

        return E

    def abstract_seq(self, seq, errs0, L):
        # don't try with short sequences
        if len(seq) < 5:
            return seq

        # try to merge last two frames
        assert len(seq) >= 2
        A1 = seq[-1].toassume()
        A2 = seq[-2].toassume()
        e1 = A1.getExpr().to_cnf()
        e2 = A2.getExpr().to_cnf()

        C1 = set(e1.children())
        C = set()
        N1 = set()
        N2 = set()
        for c in e2.children():
            if c in C1:
                C.add(c)
            else:
                N2.add(c)
        for c in C1:
            if c not in C:
                N1.add(c)

        if not C:
            return seq

        # replace last two frames with one merged frame
        EM = getGlobalExprManager()
        seq.pop()

        seq[-1].states = AssertAnnotation(EM.conjunction(*C), A1.getSubstitutions(), EM)
        S1 = AssertAnnotation(EM.conjunction(*N1), A1.getSubstitutions(), EM)
        S2 = AssertAnnotation(EM.conjunction(*N2), A2.getSubstitutions(), EM)
        seq[-1].strengthening = or_annotations(EM, True, S1, S2)

        # FIXME: we are still precies, use abstraction here...
        return seq

    def overapprox_init_seq(self, seq0, errs0, L):
        if __debug__:
            r = seq0.check_ind_on_paths(self, L.getPaths())
            assert r.errors is None, "seq is not inductive"
        S = self.getIndExecutor().createStatesSet(seq0.toannotation(True))
        EM = getGlobalExprManager()
        seq = InductiveSequence(
            overapprox_set(self, EM, S, errs0.toassert(), seq0, L).toassert()
        )
        r = seq.check_ind_on_paths(self, L.getPaths())
        # Why could this happen?
        if r.errors is None and r.ready:
            return seq
        return seq0

    def strengthen_initial_seq(self, seq0, errs0, path, L: SimpleLoop):
        # NOTE: if we would pass states here we would safe some work.. be it would be less generic
        r = seq0.check_ind_on_paths(self, L.getPaths())
        # catch it in debug mode so that we can improve...
        # assert r.errors is None, f"Initial seq is not inductive: {seq0}"
        if r.errors is None:
            dbg("Initial sequence is inductive", color="dark_green")
            return seq0

        dbg("Initial sequence is NOT inductive, trying to fix it", color="wine")
        # is the assertion inside the loop or after the loop?
        EM = getGlobalExprManager()
        assert path[0] == L._header
        createSet = self.getIndExecutor().createStatesSet
        if (path[0], path[1]) in L.get_inedges():
            # FIXME: we actually do not use the concrete assertion at all right now...
            # assertion is inside, evaluate the jump-out instruction
            # get the safe states that jump out of the loop after one iteration
            r = check_paths(self, L.getPaths())
            if not r.ready:
                return None
            ready = [
                s
                for s in r.ready
                if s.pc in (e[1].getBBlock().first() for e in L.getExits())
            ]
            if not ready:
                return None
            R = createSet()
            # FIXME: we can use only a subset of the states, wouldn't that be better?
            for r in ready:
                # do not use the first constraint -- it is the inedge condition that we want to ignore,
                # because we want to jump out of the loop (otherwise we will not get inductive set)
                C = r.getConstraints()[1:]
                expr = EM.conjunction(*C)
                expr = EM.conjunction(
                    *remove_implied_literals(expr.to_cnf().children())
                )
                tmp = createSet(r)
                tmp.reset_expr(expr)
                R.add(tmp)
            seq0 = InductiveSequence(R.as_assert_annotation())
            r = seq0.check_ind_on_paths(self, L.getPaths())
            # this may mean that the assertion in fact does not hold
            # assert r.errors is None, f"SEQ not inductive, but should be. CTI: {r.errors[0].model()}"
        else:
            r = check_paths(self, [AnnotatedCFGPath([path[0]])])
            if r.ready is None:
                return None
            R = createSet()
            ready = [s for s in r.ready if s.pc is path[1].getBBlock().first()]
            for r in ready:
                R.add(r)
            R.intersect(seq0.toannotation(True))
            seq0 = InductiveSequence(R.as_assert_annotation())
            r = seq0.check_ind_on_paths(self, L.getPaths())
            # this may mean that the assertion in fact does not hold
            # assert r.errors is None, f"SEQ not inductive, but should be. CTI: {r.errors[0].model()}"

        r = seq0.check_ind_on_paths(self, L.getPaths())
        if r.errors is None:
            dbg("Initial sequence made inductive", color="dark_green")
            return seq0
        return None

    def execute_loop(self, path, loc, states):
        unsafe = states.errors
        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False  # fall-back to loop unwinding...

        seq0, errs0 = get_initial_seq(unsafe, path, L)
        # the initial sequence may not be inductive (usually when the assertion
        # is inside the loop, so we must strenghten it
        seq0 = self.strengthen_initial_seq(seq0, errs0, path, L)
        if seq0 is None:
            return False  # we failed...

        seq0 = self.overapprox_init_seq(seq0, errs0, L)
        assert seq0

        sequences = [seq0]

        print_stdout(
            f"Executing loop {loc.getBBlockID()} with assumption", color="white"
        )
        print_stdout(str(seq0[0]), color="white")
        print_stdout(f"and errors : {errs0}")

        # NOTE: we do not require the initial (target) set to be inductive!,
        # only the rest of the sequence is inductive and it implies the target set

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- extending sequences ---")
            print_stdout(
                f"Got {len(sequences)} abstract paths of loop " f"{loc.getBBlockID()}",
                color="GRAY",
            )

            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for s, S in ((s, s.toannotation(True)) for s in sequences):
                if self.check_base(L, S):
                    print_stdout(
                        f"{S} is inductive on {loc.getBBlock().get_id()}", color="BLUE"
                    )
                    if self.genannot:
                        # maybe remember the ind set even without genannot
                        # and use it just for another 'execute_loop'?
                        loc.addAnnotationBefore(s.toannotation().Not(EM))
                    return True

            extended = []
            for seq in sequences:
                print_stdout(
                    f"Processing sequence of len {len(seq)}:\n{seq}", color="dark_blue"
                )
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.getPaths())
                    assert r.errors is None, "seq is not inductive"

                for e in self.extend_seq(seq, errs0, L):
                    extended.append(self.abstract_seq(e, errs0, L))
                # print(" -- extending DONE --")

            if not extended:
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                print_stdout("Failed extending any sequence", color="orange")
                return False  # fall-back to unwinding

            sequences = extended

    def check_base(self, L, inv):
        loc = L.header()
        dbg_sec(f"Checking if {inv} holds at loc {loc.getBBlock().get_id()}")

        def reportfn(msg, *args, **kwargs):
            dbg(f"> {msg}", *args, **kwargs)

        kindse = KindSymbolicExecutor(self.getProgram(), programstructure=self.programstructure)
        kindse.invpoints = self.invpoints
        kindse.sum_loops = self.invpoints
        kindse.reportfn = reportfn

        newpaths = []
        for p, _ in L.getEntries():
            apath = AnnotatedCFGPath([p, loc])
            apath.addLocAnnotationBefore(inv, loc)
            newpaths.append(apath)

        maxk = max(map(len, L.getPaths())) + 1
        dbg_sec("Running nested KindSE")
        res = kindse.run(newpaths, maxk=maxk, reportfn=reportfn)
        dbg_sec()
        dbg_sec()
        return res == 0

    def check_path(self, path):
        first_loc = path.first()
        if self._is_init(first_loc):
            r, states = self.checkInitialPath(path)
            if r is Result.UNSAFE:
                self.reportfn(f"Error path: {path}", color="RED")
                return r, states  # found a real error
            elif r is Result.SAFE:
                self.reportfn(f"Safe (init) path: {path}", color="DARK_GREEN")
                return None, states  # this path is safe
            elif r is Result.UNKNOWN:
                killed1 = (
                    (s for s in states.other if s.wasKilled()) if states.other else ()
                )
                killed2 = (
                    (s for s in states.early if s.wasKilled()) if states.early else ()
                )
                for s in join_iter(killed1, killed2):
                    self.report(s, self.reportfn)
                self.reportfn(f"Inconclusive (init) path: {path}")
                self.have_problematic_path = True
                # there is a problem with this path,
                # but we can still find an error
                # on some different path
                # FIXME: keep it in queue so that
                # we can rule out this path by
                # annotations from other paths?
                return None, states
            assert r is None, r

        r = self.executePath(path)

        killed1 = (s for s in r.other if s.wasKilled()) if r.other else ()
        killed2 = (s for s in r.early if s.wasKilled() or (s.hasError() and
                                                           s.getError().isMemError())) if r.early else ()
        problem = False
        for s in join_iter(killed1, killed2):
            problem = True
            self.report(s, fn=self.reportfn)
            self.reportfn(f"Killed states when executing {path}")
            self.have_problematic_path = True

        if r.errors:
            self.reportfn(f"Possibly error path: {path}", color="ORANGE")
        elif problem:
            self.reportfn(f"Problem path: {path}", color="PURPLE")
        else:
            self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        return None, r

    def findInvPoints(self, cfg):
        points = []

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                points.append(end)

        if __debug__:
            with self.new_output_file(f"{cfg.fun().getName()}-dfs.dot") as f:
                DFSVisitor().dump(cfg, f)

        DFSVisitor().foreachedge(cfg.entry(), processedge)

        return points

    def initializePaths(self, k=1):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        for F in self.programstructure.callgraph.funs():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            invpoints = self.findInvPoints(cfg)
            self.invpoints[cfg] = invpoints
            self.sum_loops[cfg] = invpoints

            nodes = cfg.getNodes()
            npaths = [AnnotatedCFGPath([n]) for n in nodes if n.hasAssert()]
            step = self.getOptions().step
            while k > 0:
                npaths = [
                    np
                    for p in npaths
                    for np in self.extendPath(
                        p, None, steps=step, atmost=True, stoppoints=invpoints
                    )
                ]
                k -= 1
            paths += npaths

        return paths

    def get_path_to_run(self):
        ready = self.readypaths
        if not ready:
            ready = self.stalepaths
        if ready:
            if len(ready) % 4 == 0:
                # do not run DFS so that we do not starve
                # some path indefinitely, but prefer the
                # lastly added paths...
                ready[-1], ready[0] = ready[0], ready[-1]
            return ready.pop()
        return None

    def is_inv_loc(self, loc):
        assert isinstance(loc, CFG.AnnotatedNode), loc
        return loc in self.invpoints[loc.getCFG()]

    def queue_paths(self, paths):
        is_inv_loc = self.is_inv_loc
        for p in paths:
            if is_inv_loc(p.first()):
                self.stalepaths.append(p)
            else:
                self.readypaths.append(p)

    def extend_and_queue_paths(self, path, states):
        step = self.getOptions().step
        newpaths = self.extendPath(
            path,
            states,
            steps=step,
            atmost=step != 1,
            stoppoints=self.invpoints[path[0].getCFG()],
        )
        self.queue_paths(newpaths)

    def run(self, paths=None, maxk=None, reportfn=print_stdout):
        k = 1

        if paths is None:
            paths = self.initializePaths()
        self.queue_paths(paths)

        while True:
            dbg(
                f"Got {len(self.readypaths)} paths ready and {len(self.stalepaths)} waiting"
            )

            path = self.get_path_to_run()
            if path is None:
                if self.have_problematic_path:
                    reportfn(
                        "Enumerating paths finished, but a problem was met.",
                        color="ORANGE",
                    )
                    return 1

                reportfn("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s, reportfn)
                reportfn("Error found.", color="RED")
                return 1
            elif states.errors:  # got error states that may not be real
                assert r is None
                fl = path.first()
                if self.is_inv_loc(fl) and fl in self.sum_loops[fl.getCFG()]:
                    if not self.handle_loop(fl, path, states):
                        # falled-back to unwinding
                        # XXX: could we try again later?
                        self.extend_and_queue_paths(path, states)
                else:
                    # normal path or a loop that we cannot summarize
                    self.extend_and_queue_paths(path, states)

            k += 1
            if maxk and maxk <= k:
                reportfn(
                    "Hit the maximal number of iterations, giving up.", color="ORANGE"
                )
                return 1
