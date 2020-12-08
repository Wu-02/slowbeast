from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions
from .kindsebase import check_paths

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    or_annotations,
)

from slowbeast.solvers.solver import getGlobalExprManager

from .loops import SimpleLoop
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence
from .overapproximations import remove_implied_literals, overapprox_set


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


def join_iter(i1, i2):
    yield from i1
    yield from i2

def overapprox(executor, s, unsafeAnnot, seq, L):
    S = executor.getIndExecutor().createStatesSet(s)
    EM = s.getExprManager()
    return overapprox_set(executor, EM, S, unsafeAnnot, seq, L)


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

    def initializePaths(self, k=1):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        PS = self.programstructure
        for F in PS.callgraph.funs():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            invpoints = PS.get_loop_headers(cfg)
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
