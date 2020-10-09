from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from . paths import SimpleLoop
from . annotations import InvariantGenerator, exec_on_loop, get_inv_candidates
from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . utils import state_to_annotation, states_to_annotation, unify_annotations

def abstract(r, post):
    print([x for x in get_inv_candidates(r)])
    for inv in get_inv_candidates(r):
        return inv
    return None
    
def strengthen(executor, prestates, A, Sind, loc, L):
    # FIXME: make A assume, not assert... or?
    T = unify_annotations(A, Sind, getGlobalExprManager(), toassert=True)
    r = exec_on_loop(loc, executor, L, pre=[A], post=[T])
    while r.errors:
       #print('pre', A)
       #print('post', T)
       #print(r)
        s = r.errors[0]
        EM = s.getExprManager()
        expr = A.getExpr()
        for l in s.getNondetLoads():
            c = s.concretize(l)[0]
            assert c is not None, "Unhandled solver failure"
            lt = s.is_sat(EM.Lt(l, c))
            if lt is False and any(map(lambda s: s.is_sat(EM.Gt(l, c)), prestates.ready)):
                expr = EM.And(expr, EM.Gt(l, c))
                break
            elif s.is_sat(EM.Gt(l, c)) is False and\
                 any(map(lambda s: s.is_sat(EM.Lt(l, c)), prestates.ready)):
                expr = EM.And(expr, EM.Lt(l, c))
                break

        A = AssumeAnnotation(expr, A.getSubstitutions(), EM)
        T = unify_annotations(A, Sind, getGlobalExprManager(), toassert=True)
        r = exec_on_loop(loc, executor, L, pre=[A], post=[T])

    if not r.errors:
        return A
    # we failed...
    return None

def check_inv(prog, loc, L, invs):
    dbg_sec(
        f"Checking if {invs} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    newpaths = []
    for p in L.getEntries():
        apath = AnnotatedCFGPath([p, loc])
        for inv in invs:
            apath.addLocAnnotationBefore(inv, loc)
        newpaths.append(apath)

    maxk=5
    dbg_sec("Running nested KindSE")
    res = kindse.run(newpaths, maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0



class KindSymbolicExecutor(BaseKindSE):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions(),
            genannot=True):
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

    def handle_loop(self, loc, states):
        self.loops.setdefault(loc.getBBlockID(), []).append(states)

       #if any(map(lambda p: self.is_inv_loc(p.first()), self.stalepaths)) or\
       #   any(map(lambda p: self.is_inv_loc(p.first()), self.readypaths)):
       #   return

        assert self.loops.get(loc.getBBlockID())
        self.execute_loop(loc, self.loops.get(loc.getBBlockID()))

    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            raise NotImplementedError("We must execute the loop normally")
            return None

        # NOTE: Safe states are the complement of error states,
        # but are not inductive on the loop header -- what we need is to
        # have safe states that already left the loop (i.e., complement of
        # error states intersected with the negation of loop condition).
        # Ready and terminated states on the paths from header to the error
        # could be used, but are not all the safe states (there may be safe
        # states that miss the assertion)

        S = None # safe states
        H = None # negation of loop condition
        for u in unsafe:
            EM = u.getExprManager()
            S = unify_annotations(S or AssumeAnnotation(EM.getFalse(), {}, EM),
                                  state_to_annotation(u), EM)
            H = EM.Or(H or EM.getFalse(), u.getConstraints()[0])

        # FIXME: EM is out of scope
        # This is the first inductive set on H
        S = AssumeAnnotation(EM.simplify(EM.And(EM.Not(S.getExpr()), H)),
                             S.getSubstitutions(), EM)
        Serr = AssertAnnotation(S.getExpr(), S.getSubstitutions(), EM)
        #print('F0', S)
        if __debug__:
            r = exec_on_loop(loc, self, L, pre=[S], post=[Serr])
            assert r.errors is None


        # FIXME: EM is out of scope
        print('--- starting executing ---')
        EM = getGlobalExprManager()
        while True:
            print('--- iter ---')
            r = exec_on_loop(loc, self, L, pre=[Serr.Not(EM)], post=[Serr])
            if r.errors is None:
                break
            #print('Target', Serr)

            # NOTE: we must use Not(r.errors), r.ready does not yield inductive set
            # for some reason... why? Why, oh, why? One would think they are
            # complements... 
            A = abstract(r, Serr)
            print(Serr)
            print(A)
            if A is None:
                A = states_to_annotation(r.errors).Not(EM)
                S = A
            else:
                S = strengthen(self, r, A, Serr, loc, L)
                if S is None:
                    S = states_to_annotation(r.errors).Not(EM)
           #print('Strengthened', S)
           #print('Abstracted', A)

            S = unify_annotations(S, Serr, EM)
            Serr = AssertAnnotation(S.getExpr(), S.getSubstitutions(), EM)
            if __debug__:
                # debugging check -- S should be now inductive on loc
                r = exec_on_loop(loc, self, L, pre=[S], post=[Serr])
                assert r.errors is None, "S is not inductive"
                print("S is inductive...")

            if check_inv(self.getProgram(), loc, L, [Serr]):
                print_stdout(f"{S} is invariant of loc {loc.getBBlock().getID()}",
                             color="BLUE")
                loc.annotationsBefore.append(S)
                break

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
                    print_stdout("Enumerating paths finished, but a problem was met.", color='ORANGE')
                    return 1

                print_stdout("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color='RED')
                return 1
            elif states.errors: # got error states that may not be real
                assert r is None
                if self.is_inv_loc(path.first()):
                    self.handle_loop(path.first(), states)
                else:
                    self.extend_and_queue_paths(path)

            k += 1
            if maxk and maxk <= k:
                print_stdout(
                    "Hit the maximal number of iterations, giving up.",
                    color='ORANGE')
                return 1
