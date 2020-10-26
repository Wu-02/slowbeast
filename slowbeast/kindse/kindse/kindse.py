from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import (
    KindSymbolicExecutor as BasicKindSymbolicExecutor,
)
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.annotations import (
    AssumeAnnotation,
    AssertAnnotation,
    state_to_annotation,
    states_to_annotation,
    or_annotations,
    and_annotations,
    unify_annotations,
)
from slowbeast.symexe.statesset import StatesSet
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from .loops import SimpleLoop
from .relations import get_safe_relations, get_safe_subexpressions
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence


def overapproximations(s, unsafe):
    yield from get_safe_relations([s], unsafe)
    yield from get_safe_subexpressions(s, unsafe)


def strengthenIndFromTop(executor, s, a, seq, L):
    """
    Strengthen 'a' which is the abstraction of 's' w.r.t 'seq' and 'L'
    so that a \cup seq is inductive.
    """
    # print(f'Strengthening {a}')
    EM = getGlobalExprManager()
    solver = s.getSolver()

    assert isinstance(a, InductiveSequence.Frame)

    # execute {a} L {seq + a}
    r = seq.check_on_paths(executor, L.getPaths(), pre=[a.toassume()], tmpframes=[a])
    if not r.errors:  # the abstraction is inductive w.r.t seq
        return a

    newframe = InductiveSequence.Frame(a.states, a.strengthening)
    S = []  # strengthening
    while r.errors:
        for e in r.errors:
            Schanged = False
            m = e.model()
            for (x, c) in m.items():
                if c is None:
                    continue
                # Try extend the cex value such that it implies
                # the original state (that's required to be
                # a correct abstraction)
                G = EM.Ge(x, c)
                if s.is_sat(G, *S) is False:
                    # x < c
                    # try to push c as far as we can
                    cp = EM.freshValue("c", c.getType().getBitWidth())
                    cpval = s.concretize_with_assumptions(
                        [*S, EM.Lt(cp, c), EM.Gt(x, cp)], cp
                    )
                    if cpval:
                        expr = EM.Lt(x, cpval[0])
                    else:
                        expr = EM.Not(G)
                    if solver.is_sat(expr, *S) is True:
                        # append the expr but only if it does
                        # not break the others...
                        S.append(expr)
                        Schanged = True

                G = EM.Le(x, c)
                if s.is_sat(G, *S) is False:
                    cp = EM.freshValue("c", c.getType().getBitWidth())
                    # x > c
                    cpval = s.concretize_with_assumptions(
                        [*S, EM.Gt(cp, c), EM.Lt(x, cp)], cp
                    )
                    if cpval:
                        expr = EM.Gt(x, cpval[0])
                    else:
                        expr = EM.Not(G)

                    expr = EM.Not(G)
                    if solver.is_sat(expr, *S) is True:
                        S.append(expr)
                        Schanged = True

        if not Schanged:
            break
        origstren = a.strengthening
        stren = EM.conjunction(*S, origstren.getExpr())
        newframe.strengthening = AssumeAnnotation(
            stren, origstren.getSubstitutions(), EM
        )
        # check with the new frame
        r = seq.check_on_paths(
            executor, L.getPaths(), pre=[newframe.toassume()], tmpframes=[newframe]
        )

    if not r.errors:
        return newframe
    # we failed...
    return InductiveSequence.Frame(state_to_annotation(s), None)


def _simplify_with_assumption(lhs, rhs):
    """
    Remove from 'rhs' (some) parts implied by the 'lhs'
    'rhs' is a list of Or expressions
    'lhs' is a list of Or expressions
    """
    # FIXME do this with an incremental solver
    assumptions = lhs.copy()

    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in rhs:
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)

    assumptions += singletons

    # remove the implied parts of the rest of clauses
    changed = False
    newrhs = []
    newsingletons = []
    solver = Solver()
    EM = getGlobalExprManager()
    Not = EM.Not
    for c in rest:
        newliterals = []
        for l in c.children():
            assert l.isBool()
            q = solver.is_sat(*assumptions, l)
            if q is not False:
                q = solver.is_sat(*assumptions, Not(l))
                if q is False:
                    # this literal is implied and thus the whole clause is true
                    changed = True
                    break
                else:
                    # we know that the literal can be true
                    # or the solver failed, so keep the literal
                    newliterals.append(l)
            else:
                # we dropped the literal
                changed = True

        assert len(newliterals) > 0, "Unsat clause..."
        if len(newliterals) == 1:
            # XXX: we could do this also for non-singletons,
            # but do we want to?
            assumptions.append(literals[0])
            newsingletons.append(literals[0])
        else:
            newrhs.append(newliterals)

    # get rid of redundant singletons
    assumptions = lhs.copy()
    tmp = []
    for c in singletons:
        assert c.isBool()
        q = solver.is_sat(*assumptions, Not(c))
        if q is False:
            # this literal is implied and we can drop it
            changed = True
            continue
        else:
            # we know that the literal can be true
            # or the solver failed, so keep the literal
            tmp.append(c)
    singletons = tmp

    return newsingletons, singletons + newrhs, changed


def simplify_with_assumption(lhs, rhs):
    lhs = list(lhs.to_cnf().children())
    rhs = list(rhs.to_cnf().children())
    changed = True

    while changed:
        singletons, rhs, changed = _simplify_with_assumption(lhs, rhs)
        lhs += singletons

    return getGlobalExprManager().conjunction(*rhs)


def strengthenInd(executor, s, a, seq, L):
    """
    Strengthen 'a' which is the abstraction of 's' w.r.t 'seq' and 'L'
    so that a \cup seq is inductive.
    """
    print(f"Strengthening {a}")
    EM = getGlobalExprManager()
    solver = s.getSolver()

    assert isinstance(a, InductiveSequence.Frame)

    subs = a.states.getSubstitutions()
    abstraction = a.states.getExpr()
    strengthening = a.strengthening.getExpr() if a.strengthening else None

    constraints = s.getConstraintsObj().asFormula(EM)
    strengthening = simplify_with_assumption(
        abstraction,
        EM.And(constraints, strengthening) if strengthening else constraints,
    )

    st = StatesSet(s)
    print(st)
    st.unite(a.states)
    print(st)
    st.intersect(a.strengthening)
    print(st)
    assert False

    # execute {a} L {seq + a}
    if __debug__:
        a = InductiveSequence.Frame(
            AssumeAnnotation(abstraction, subs, EM),
            AssumeAnnotation(strengthening, subs, EM),
        )

        print("Decomposition: ", a)
        r = seq.check_on_paths(
            executor, L.getPaths(), pre=[a.toassume()], tmpframes=[a]
        )
        assert r.errors is None, "The non-abstracted set of states is not inductive"

    while True:  # the abstraction is inductive w.r.t seq
        # try to drop whole clauses
        for chld in strengthening.children():
            tmp = EM.simplify(EM.substitute(strengthening, (chld, EM.getTrue())))

            a = InductiveSequence.Frame(
                AssumeAnnotation(abstraction, subs, EM), AssumeAnnotation(tmp, subs, EM)
            )

            r = seq.check_on_paths(
                executor, L.getPaths(), pre=[a.toassume()], tmpframes=[a]
            )
            if r.errors is None:
                strengthening = tmp

        break

    a = InductiveSequence.Frame(
        AssumeAnnotation(abstraction, subs, EM),
        AssumeAnnotation(strengthening, subs, EM),
    )

    if __debug__:
        r = seq.check_on_paths(
            executor, L.getPaths(), pre=[a.toassume()], tmpframes=[a]
        )
        assert r.errors is None, "The non-abstracted set of states is not inductive"

    print(f"Strengthened to {a}")
    return a  # return the best we have


def abstract(executor, state, unsafe):
    """
    unsafe - unsafe states from the last step
    """
    yield from overapproximations(state, unsafe)


def strengthenSafe(executor, s, a, seq, errs0, L):
    # if the annotations intersect, remove errs0 from a
    EM = getGlobalExprManager()

    # FIXME: proceed only when a intersects errs0

    # NOTE: the strengthening is the loop-exit condition.
    # It is sufficient to exclude the unsafe states
    states, stren, subs, noterrstates = None, None, None, None
    if errs0.strengthening:
        if a.strengthening is None:
            noterrstates = errs0.strengthening.Not(EM)
        else:
            noterrstates = and_annotations(
                EM, True, a.strengthening, errs0.strengthening.Not(EM)
            )
    else:
        # the error loc is inside a loop - we must use the whole error
        # states decription
        # FIXME: try use only a part of the condition (unsat core)
        assert errs0.states
        if a.strengthening is None:
            noterrstates = errs0.states.Not(EM)
        else:
            noterrstates = and_annotations(
                EM, True, a.strengthening, errs0.states.Not(EM)
            )
    states, stren, subs = unify_annotations(EM, a.states, noterrstates)
    A1 = AssertAnnotation(states, subs, EM)
    A2 = AssertAnnotation(stren, subs, EM)
    return InductiveSequence.Frame(A1, A2)


def check_inv(prog, L, inv):
    loc = L.loc
    dbg_sec(f"Checking if {inv} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    newpaths = []
    for p in L.getEntries():
        apath = AnnotatedCFGPath([p, loc])
        apath.addLocAnnotationBefore(inv, loc)
        newpaths.append(apath)

    maxk = 5
    dbg_sec("Running nested KindSE")
    res = kindse.run(newpaths, maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0


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
    E = None  # safe states
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

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sh = AssertAnnotation(H, subs, EM)
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, Sh), InductiveSequence.Frame(Se, Sh)


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
        maxk = 5
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
        r = seq.check_last_frame(self, L.getPaths())
        if not r.ready:  # cannot step into this frame...
            # FIXME we can use it at least for annotations
            dbg("Infeasible frame...")
            return []

        EM = getGlobalExprManager()
        E = []
        checked_abstractions = set()
        for s in r.ready:
            for a in abstract(self, s, r.errors):
                if a in checked_abstractions:
                    continue
                checked_abstractions.add(a)
                # dbg('Abstraction: ', a)

                # strengthen S such that it is safe (does not
                # intersect the errs0 states
                F = InductiveSequence.Frame(a, None)
                S = strengthenSafe(self, s, F, seq, errs0, L)
                if S is None:
                    print("Failed strengthening to safe states")
                    continue
                # inductively strengthen s
                S = strengthenInd(self, s, S, seq, L)
                # this does not work...
                if S != seq[-1]:
                    if S:
                        tmp = seq.copy()
                        tmp.append(S.states, S.strengthening)
                        E.append(tmp)
                        # we have one strengthened abstraction,
                        # it is enough
                        break
                    # print('== extended to == ')
                    # print(tmp)
        return E

    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False  # fall-back to loop unwinding...

        # FIXME: strengthen seq0
        seq0, errs0 = get_initial_seq(unsafe)
        sequences = [seq0]

        print_stdout(f"Executing loop {loc.getBBlockID()} with assumption")
        print_stdout(str(seq0[0]))
        print_stdout(f"and errors : {errs0}")

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- iter ---")
            E = []
            print_stdout(
                f"Got {len(sequences)} abstract paths of loop " f"{loc.getBBlockID()}",
                color="GRAY",
            )
            for seq in sequences:
                print_stdout(f"Processing sequence of len {len(seq)}")
                print("Processing seq:\n", seq)
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.getPaths())
                    assert r.errors is None, "seq is not inductive"

                E += self.extend_seq(seq, errs0, L)
                # print(' -- extending DONE --')

            if not E:
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                return False  # fall-back to unwinding

            # FIXME: check that all the sequences together
            # cover the input paths
            for s, S in ((s, s.toannotation(True)) for s in E):
                if check_inv(self.getProgram(), L, S):
                    print_stdout(
                        f"{S} is inductive on {loc.getBBlock().getID()}", color="BLUE"
                    )
                    if self.genannot:
                        # maybe remember the ind set even without genannot
                        # and use it just for another 'execute_loop'?
                        loc.addAnnotationBefore(s.toannotation().Not(EM))
                    return True
            sequences = E

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
                killed = (
                    (s for s in states.other if s.wasKilled()) if states.other else ()
                )
                for s in killed:
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

        killed = (s for s in r.other if s.wasKilled()) if r.other else ()
        for s in killed:
            self.report(s)
            self.reportfn(f"Killed states when executing {path}")
            self.have_problematic_path = True

        if r.errors:
            self.reportfn(f"Possibly error path: {path}", color="ORANGE")
        else:
            self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        return None, r

    def findInvPoints(self, cfg):
        points = []

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                points.append(end)

        if __debug__:
            with self.new_output_file(f"{cfg.getFun().getName()}-dfs.dot") as f:
                DFSVisitor().dump(cfg, f)

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        for F in self.callgraph.getFunctions():
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
