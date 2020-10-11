from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from . loops import SimpleLoop
from . relations import get_safe_relations, get_safe_subexpressions
from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . utils import state_to_annotation, states_to_annotation, or_annotations
from . inductivesequence import InductiveSequence


def overapproximations(s, unsafe):
    yield from get_safe_relations([s], unsafe)
    yield from get_safe_subexpressions(s, unsafe)

def strengthen(executor, s, a, seq, L):
    """
    Strengthen 'a' which is the abstraction of 's' w.r.t 'seq' and 'L'
    """
    #print(f'Strengthening {a}')
    EM = getGlobalExprManager()
    solver = s.getSolver()

    newframe = InductiveSequence.Frame(a, None)
    # execute {a} L {seq + a}
    r = seq.check_on_paths(executor, L.getPaths(),
                           pre=[a], tmpframes = [newframe])
    if not r.errors: # the abstraction is inductive w.r.t seq
        return newframe
    S = [] #strengthening
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
                    #x < c
                    # try to push c as far as we can
                    cp = EM.freshValue('c', c.getType().getBitWidth())
                    cpval = s.concretize_with_assumptions(
                            [*S, EM.Lt(cp, c), EM.Gt(x, cp)],
                            cp)
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
                    cp = EM.freshValue('c', c.getType().getBitWidth())
                    #x > c
                    cpval = s.concretize_with_assumptions(
                            [*S, EM.Gt(cp, c), EM.Lt(x, cp)],
                            cp)
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
        newframe = InductiveSequence.Frame(a,
                              AssumeAnnotation(EM.conjunction(*S),
                                               a.getSubstitutions(),
                                               EM))
        r = seq.check_on_paths(executor, L.getPaths(),
                               pre=[newframe.toassume()],
                               tmpframes = [newframe])

    if not r.errors:
        return newframe
    # we failed...
    return InductiveSequence.Frame(state_to_annotation(s), None)

def abstract(executor, state, unsafe):
    yield from overapproximations(state, unsafe)

def check_inv(prog, L, inv):
    loc = L.loc
    dbg_sec(
        f"Checking if {inv} is invariant of loc {loc.getBBlock().getID()}")

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
        # NOTE: Only safe states that reach the assert are not inductive on the
        # loop header -- what we need is to have safe states that already left
        # the loop and safely pass assertion or avoid it.
        # These are the complement of error states intersected with the
        # negation of loop condition.

        S = None  # safe states
        H = None  # loop exit condition

        EM = getGlobalExprManager()
       #for u in unsafe:
       #    S = or_annotations(EM, True,
       #                       S or AssumeAnnotation(EM.getFalse(), {}, EM),
       #                       state_to_annotation(u))
       #    H = EM.Or(H or EM.getFalse(), u.getConstraints()[0])
       #notS = EM.simplify(EM.Not(S.getExpr()))
       #S = AssertAnnotation(EM.And(H, notS), S.getSubstitutions(), EM)

        for u in unsafe:
            # constraints without loop exit condition
            uconstr = u.getConstraints()
            notu = EM.disjunction(*map(EM.Not, uconstr[1:]))
            S = EM.And(notu, S) if S else notu # use conjunction too?
            # loop exit condition
            H = EM.Or(H, uconstr[0]) if H else uconstr[0]

        Sa = AssertAnnotation(EM.And(H, S),
                              {l : l.load for l in unsafe[0].getNondetLoads()},
                              EM)
        return InductiveSequence(Sa)

class KindSymbolicExecutor(BaseKindSE):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions(),
            genannot=False):
        super(
            KindSymbolicExecutor,
            self).__init__(
            prog=prog,
            testgen=testgen,
            opts=opts)

        self.readypaths = []
        self.stalepaths = []

        self.genannot = genannot
        self.invpoints = {}
        self.have_problematic_path = False
        self.loops = {}
        self.sum_loops = {}

    def handle_loop(self, loc, path, states):
        self.loops.setdefault(loc.getBBlockID(), []).append(states)

        assert loc in self.sum_loops[loc.getCFG()],\
                "Handling a loop that should not be handled"

        # first try to unroll it in the case the loop
        # is easy to verify
        kindse = BaseKindSE(self.getProgram())
        maxk = 5
        dbg_sec("Running nested KindSE")
        res = kindse.run([path.copy()], maxk=maxk)
        dbg_sec()
        if res == 0:
            print_stdout(f"Loop {loc.getBBlockID()} proved by the basic KindSE",
                         color="GREEN")
            return True

        assert self.loops.get(loc.getBBlockID())
        if not self.execute_loop(loc, self.loops.get(loc.getBBlockID())):
            self.sum_loops[loc.getCFG()].remove(loc)
            print_stdout(f"Falling back to unwinding loop {loc.getBBlockID()}",
                         color="BROWN")
            return False
        return True

    def to_distinct(self, frame1, frame2):
        """
        return frame1 \ frame2 if frame1 and frame2 have intersection,
        otherwise return frame1
        """
        assert frame1
        assert frame2

        #XXX
        return frame1

        executor = self.getIndExecutor()
        tmps = executor.createState()
        tmps.pushCall(None, self.getProgram().getEntry())

        class DummyInst:
            def getNextInstruction(self):
                return self

        #FIXME: do it part by part (so that we do not create the and
        #formulas in toassume()
        states, nonr = executor.executeAnnotation([tmps], frame1.toassume(), DummyInst())
        assert states and not nonr and len(states) == 1
        tmps2 = states[0].copy()
        # FIXME: do this only when they have intersection
        states, nonr = executor.executeAnnotation(states, frame2.toassume(), DummyInst())
        assert not nonr
        if states: # they have intersection
            assert len(states) == 1
            notframe2 = frame2.toassume().Not(tmps.getExprManager())
            states, nonr = executor.executeAnnotation([tmps2], notframe2, DummyInst())
            if states:
                # FIXME: we broke 'states + strength' structure
                return InductiveSequence.Frame(states_to_annotation(states), None)
            # they are implied
            return None
        return frame1

    def extend_seq(self, seq, L):
        r = seq.check_last_frame(self, L.getPaths())
        if not r.ready: # cannot step into this frame...
            # FIXME we can use it at least for annotations
            dbg('Infeasible frame...')
            return []

        EM = getGlobalExprManager()
        E = []
        checked_abstractions = set()
        for s in r.ready:
            for a in abstract(self, s, r.errors):
                if a in checked_abstractions:
                    continue
                checked_abstractions.add(a)
                #dbg('Abstraction: ', a)

                S = strengthen(self, s, a, seq, L)
                if S != seq[-1]:
                   #solver = s.getSolver()
                   #for e in E:
                   #    S = self.to_distinct(S, e[-1])
                   #    if S is None:
                   #        break
                    if S:
                        tmp = seq.copy()
                        tmp.append(S.states, S.strengthening)
                        E.append(tmp)
                       #print('== extended to == ')
                       #print(tmp)
        return E


    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False # fall-back to loop unwinding...

        # FIXME: strengthen
        sequences = [get_initial_seq(unsafe)]

        print_stdout(f"Executing loop {loc.getBBlockID()} with assumption")
        print_stdout(str(sequences[0][0].states))

        #print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            #print('--- iter ---')
            E = []
            for seq in sequences:
                print_stdout(f"Got {len(sequences)} abstract paths of loop "
                             f"{loc.getBBlockID()}", color="GRAY")
                #print('Processing seq:\n', seq)
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.getPaths())
                    assert r.errors is None, 'seq is not inductive'

                E += self.extend_seq(seq, L)
                #print(' -- extending DONE --')

            if not E:
               #seq not extended... it looks that there is no
               #safe invariant
               #FIXME: could we use it for annotations?
               return False # fall-back to unwinding

            # FIXME: check that all the sequences together
            # cover the input paths
            for s, S in ((s, s.toannotation(True)) for s in E):
                 if check_inv(self.getProgram(), L, S):
                     print_stdout(
                         f"{S} is inductive on {loc.getBBlock().getID()}",
                         color="BLUE")
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
                killed = (s for s in states.other if s.wasKilled())\
                    if states.other else ()
                for s in killed:
                    self.report(s)
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

        killed = (s for s in r.other if s.wasKilled()) if r.other else None
        if killed:
            self.have_problematic_path = True
            for s in killed:
                self.report(s)

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

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        paths = []
        for F in self.getProgram().getFunctions():
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
                    np for p in npaths for np in self.extendPath(
                        p, steps=step, atmost=True,
                        stoppoints=invpoints)]
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

    def extend_and_queue_paths(self, path):
        step = self.getOptions().step
        newpaths = self.extendPath(path,
                                   steps=step,
                                   atmost=step != 1,
                                   stoppoints=self.invpoints[path[0].getCFG()])
        self.queue_paths(newpaths)

    def run(self, paths=None, maxk=None):
        k = 1

        if paths is None:
            paths = self.initializePaths()
        self.queue_paths(paths)

        while True:
            dbg(f"Got {len(self.readypaths)} paths ready and {len(self.stalepaths)} waiting")

            path = self.get_path_to_run()
            if path is None:
                if self.have_problematic_path:
                    print_stdout(
                        "Enumerating paths finished, but a problem was met.",
                        color='ORANGE')
                    return 1

                print_stdout("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color='RED')
                return 1
            elif states.errors:  # got error states that may not be real
                assert r is None
                fl = path.first()
                if self.is_inv_loc(fl) and fl in self.sum_loops[fl.getCFG()]:
                    if not self.handle_loop(fl, path, states):
                        # falled-back to unwinding
                        # XXX: could we try again later?
                        self.extend_and_queue_paths(path)
                else:
                    # normal path or a loop that we cannot summarize
                    self.extend_and_queue_paths(path)

            k += 1
            if maxk and maxk <= k:
                print_stdout(
                    "Hit the maximal number of iterations, giving up.",
                    color='ORANGE')
                return 1
