from functools import partial

from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import IntType
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.core.executor import PathExecutionResult
from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import (
    KindSymbolicExecutor as BasicKindSymbolicExecutor,
)
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    or_annotations,
)

from slowbeast.symexe.statesset import union, intersection, complement
from slowbeast.solvers.solver import getGlobalExprManager, Solver
from slowbeast.solvers.expressions import em_optimize_expressions

from .loops import SimpleLoop
from .relations import get_safe_relations, get_safe_subexpressions
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence


def remove_implied_literals(clauses):
    """
    Returns an equivalent but possibly smaller formula
    """

    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in clauses:
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)

    EM = getGlobalExprManager()
    Not = EM.Not
    solver = Solver()
    newclauses = []
    # NOTE: we could do this until a fixpoint, but...
    for r in rest:
        changed = False
        drop = False
        newc = []
        for l in r.children():
            if solver.is_sat(*singletons, l) is False:
                dbg(f"Dropping {l}, it's False")
                changed = True
            elif solver.is_sat(*singletons, Not(l)) is False:
                # XXX: is it worth querying the solver for this one?
                drop = True
                break
            else:
                newc.append(l)
        if drop:
            dbg(f"Dropping {r}, it's True")
            continue
        elif changed:
            if len(newc) == 1:
                singletons.append(newc[0])
            else:
                newclauses.append(EM.disjunction(*newc))
        else:
            newclauses.append(r)

    return singletons + newclauses


def check_base(prog, L, inv):
    loc = L.loc
    dbg_sec(f"Checking if {inv} is invariant of loc {loc.getBBlock().get_id()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    newpaths = []
    for p in L.getEntries():
        apath = AnnotatedCFGPath([p, loc])
        apath.addLocAnnotationBefore(inv, loc)
        newpaths.append(apath)

    maxk = max(map(len, L.getPaths())) + 1
    dbg_sec("Running nested KindSE")
    res = kindse.run(newpaths, maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0


def get_initial_seq2(unsafe):
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
    H = None  # loop exit condition

    EM = getGlobalExprManager()
    Not = EM.Not
    for u in unsafe:
        # add constraints without loop exit condition
        # (we'll add the loop condition later)
        uconstr = u.getConstraints()
        # same as uconstr[1:], but via generators
        uconstrnh = (c for (n, c) in enumerate(uconstr) if n > 0)
        # safe states
        notu = EM.disjunction(*map(Not, uconstrnh))
        S = EM.And(notu, S) if S else notu  # use conjunction too?
        # unsafe states
        su = EM.conjunction(*(c for (n, c) in enumerate(uconstr) if n > 0))
        E = EM.Or(su, E) if E else su

        # loop exit condition
        H = EM.Or(H, uconstr[0]) if H else uconstr[0]

    # simplify the formulas
    if not S.is_concrete():
        S = EM.conjunction(*remove_implied_literals(list(S.to_cnf().children())))
    if not E.is_concrete():
        E = EM.conjunction(*remove_implied_literals(list(E.to_cnf().children())))
    if not H.is_concrete():
        H = EM.conjunction(*remove_implied_literals(list(H.to_cnf().children())))

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sh = AssertAnnotation(H, subs, EM)
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    # solver = Solver()
    # if solver.is_sat(S, E) is False:
    #    # if safe states themselves do not intersect the error states,
    #    # we can use them without the loop-exit condition
    #    # FIXME: we could also drop some clauses...
    #    clauses = list(S.to_cnf().children())
    #    changed = False
    #    for c in S.to_cnf().children():
    #        # XXX: we could do this until a fixpoint
    #        tmp = clauses.copy()
    #        tmp.remove(c)
    #        if solver.is_sat(E, EM.conjunction(*tmp)) is False:
    #            changed = True
    #            clauses = tmp
    #    if changed:
    #        Sa = AssertAnnotation(EM.conjunction(*clauses), subs, EM)
    #    return InductiveSequence(Sa), InductiveSequence.Frame(Se, Sh)

    return InductiveSequence(Sa, Sh), InductiveSequence.Frame(Se, Sh)

def get_initial_seq(unsafe):
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
    Not = EM.Not
    for u in unsafe:
        # add constraints without loop exit condition
        # (we'll add the loop condition later)
        uconstr = u.getConstraints()
        # all constr. apart from the last one
        pc = EM.conjunction(*uconstr[:-1])
        # last constraint is the failed assertion
        S = EM.conjunction(pc, Not(uconstr[-1]), S) if S else EM.And(pc, Not(uconstr[-1]))
        # unsafe states
        su = EM.conjunction(*(c for (n, c) in enumerate(uconstr) if n > 0))
        E = EM.Or(EM.conjunction(*uconstr), E) if E else EM.conjunction(*uconstr)

    # simplify the formulas
    if not S.is_concrete():
        S = EM.conjunction(*remove_implied_literals(list(S.to_cnf().children())))
    if not E.is_concrete():
        E = EM.conjunction(*remove_implied_literals(list(E.to_cnf().children())))

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


def overapprox_literal(l, S, unsafe, target, executor, L):
    assert not l.isAnd() and not l.isOr(), f"Input is not a literal: {l}"
    assert intersection(S, l, unsafe).is_empty(), "Unsafe states in input"
    goodl = l  # last good overapprox of l

    left, right, P, addtoleft = decompose_literal(l)
    if left is None:
        assert right is None
        return goodl

    EM = getGlobalExprManager()

    def check_literal(lit):
        if lit.is_concrete():
            return False
        X = intersection(S, lit)
        if not intersection(X, unsafe).is_empty():
            return False

        r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
        return r.errors is None and r.ready is not None

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
        num = ConcreteInt(2 ** (bw - 1) - 1, bw)

        while True:
            l = modify_literal(goodl, P, num)
            if l is None:
                return goodl

            # push as far as we can with this num
            while check_literal(l):
                goodl = l

                l = modify_literal(goodl, P, num)
                if l is None:
                    break

            if num.value() <= 1:
                return goodl
            num = EM.Div(num, two)

    em_optimize_expressions(False)
    # the optimizer could make And or Or from the literal, we do not want that...
    goodl = extend_literal(goodl)
    em_optimize_expressions(True)

    return goodl


def overapprox_clause(n, clauses, executor, L, unsafe, target):
    createSet = executor.getIndExecutor().createStatesSet

    S = createSet()
    c = None
    for i, x in enumerate(clauses):
        if i == n:
            c = x
        else:
            S.intersect(x)
    assert c

    assert intersection(S, c, unsafe).is_empty(), f"{S} \cap {c} \cap {unsafe}"

    newc = []
    for l in literals(c):
        newl = overapprox_literal(l, S, unsafe, target, executor, L)
        newc.append(newl)
        dbg(f"  Overapproximated {l} ==> {newl}")

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
            d, = c.children()
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

    createSet = executor.getIndExecutor().createStatesSet
    S = createSet(s)
    unsafe = createSet(unsafeAnnot)  # safe strengthening
    assert not unsafe.is_empty(), "Empty error states"
    assert intersection(
        S, unsafe
    ).is_empty(), f"Whata? Unsafe states among one-step reachable safe states:\nS = {S},\nunsafe = {unsafe}"

    # print_stdout(f"Overapproximating {S}", color="BROWN")
    # print_stdout(f"  with unsafe states: {unsafe}", color="BROWN")
    EM = s.getExprManager()
    target = createSet(seq[-1].toassert())

    expr = S.as_expr().to_cnf()
    #clauses = break_eq_ne(expr)
    clauses = list(expr.children())

    # can we drop a clause completely?
    newclauses = clauses.copy()
    for c in clauses:
        tmp = newclauses.copy()
        tmp.remove(c)

        tmpexpr = EM.conjunction(*tmp)
        if tmpexpr.is_concrete():
            continue  # either False or True are bad for us
        X = S.copy()
        X.reset_expr(tmpexpr)
        if not intersection(X, unsafe).is_empty():
            continue  # we can't...
        r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
        if r.errors is None and r.ready:
            newclauses = tmp
            dbg(f"  dropped {c}...")

    clauses = remove_implied_literals(newclauses)
    newclauses = []
    for n in range(0, len(clauses)):
        newclause = overapprox_clause(n, clauses, executor, L, unsafe, target)
        if newclause:
            newclauses.append(newclause)

    clauses = remove_implied_literals(newclauses)
    S.reset_expr(EM.conjunction(*clauses))

    # print_stdout(f"Overapproximated to {S}", color="BROWN")

    sd = S.as_description()
    A1 = AssertAnnotation(sd.getExpr(), sd.getSubstitutions(), EM)
    return InductiveSequence.Frame(S.as_assert_annotation(), None)

def join_iter(i1, i2):
    yield from i1
    yield from i2

class KindSymbolicExecutor(BaseKindSE):
    def __init__(self, prog, ohandler=None, opts=KindSeOptions(), genannot=False):
        super(KindSymbolicExecutor, self).__init__(
            prog=prog, ohandler=ohandler, opts=opts
        )

        self.readypaths = []
        self.stalepaths = []

        self.invpoints = {}
        self.loops = {}

        self.genannot = genannot
        self.sum_loops = {}

    def handle_loop(self, loc, path, states):
        self.loops.setdefault(loc.getBBlockID(), []).append(states)

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

        assert self.loops.get(loc.getBBlockID())
        if not self.execute_loop(loc, self.loops.get(loc.getBBlockID())):
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

    def strengthenInitialSeq(self, seq0, errs0, L):
        r = seq0.check_ind_on_paths(self, L.getPaths())
        # catch it in debug mode so that we can improve...
        #assert r.errors is None, f"Initial seq is not inductive: {seq0}"
        if r.errors is None:
            # initial sequence is not inductive
            return seq0

        return None

    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False  # fall-back to loop unwinding...

        seq0, errs0 = get_initial_seq(unsafe)
        # the initial sequence may not be inductive (usually when the assertion
        # is inside the loop, so we must strenghten it
        seq0 = self.strengthenInitialSeq(seq0, errs0, L)
        if seq0 is None:
            return False # we failed...

        sequences = [seq0]

        print_stdout(f"Executing loop {loc.getBBlockID()} with assumption")
        print_stdout(str(seq0[0]))
        print_stdout(f"and errors : {errs0}")

        # NOTE: we do not require the initial (target) set to be inductive!,
        # only the rest of the sequence is inductive and it implies the target set

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- iter ---")
            print_stdout(
                f"Got {len(sequences)} abstract paths of loop " f"{loc.getBBlockID()}",
                color="GRAY",
            )

            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for s, S in ((s, s.toannotation(True)) for s in sequences):
                if check_base(self.getProgram(), L, S):
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
                    self.report(s)
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
        killed2 = (s for s in r.early if s.wasKilled()) if r.early else ()
        problem = False
        for s in join_iter(killed1, killed2):
            problem = True
            self.report(s)
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

        DFSVisitor().foreachedge(processedge, cfg.entry())

        return points

    def initializePaths(self, k=1):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        for F in self.callgraph.funs():
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

    def run(self, paths=None, maxk=None):
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
                    print_stdout(
                        "Enumerating paths finished, but a problem was met.",
                        color="ORANGE",
                    )
                    return 1

                print_stdout("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color="RED")
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
                print_stdout(
                    "Hit the maximal number of iterations, giving up.", color="ORANGE"
                )
                return 1
