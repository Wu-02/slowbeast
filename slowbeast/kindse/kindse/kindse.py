from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from . loops import SimpleLoop
from . relations import InvariantGenerator, exec_on_loop
from . relations import get_safe_relations, get_safe_subexpressions
from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . utils import state_to_annotation, states_to_annotation, unify_annotations
from . inductivesequence import InductiveSequence


def overapproximations(r):
    yield from get_safe_relations(r.ready, r.errors)
    for s in r.ready:
        yield from get_safe_subexpressions(s, r.errors)

def strengthen(executor, seq, L):
    """ Strengthen the last frame of the sequence """

    EM = getGlobalExprManager()
    r = seq.check_ind_on_paths(executor, L.getPaths())
    while r.errors:
        s = r.errors[0]
        for l in s.getNondetLoads():
            c = s.concretize(l)[0]
            assert c is not None, "Unhandled solver failure"
            lt = s.is_sat(EM.Lt(l, c))
            if lt is False and any(
                    map(lambda s: s.is_sat(EM.Gt(l, c)), prestates.ready)):
                seq.strengthen(EM.Gt(l, c))
                break
            elif s.is_sat(EM.Gt(l, c)) is False and\
                    any(map(lambda s: s.is_sat(EM.Lt(l, c)), prestates.ready)):
                seq.strengthen(EM.Lt(l, c))
                break

        r = seq.check_ind_on_paths(executor, L.getPaths())

    if not r.errors:
        return seq
    # we failed...
    return None

def abstract(executor, L, states, seq):
    EM = getGlobalExprManager()
    for A in overapproximations(states):
        print('Overapprox:', A)

        tmp = seq.copy()
        tmp.append(A, None)
        S = strengthen(executor, tmp, L)
        if S:
            return S
    return None


def check_inv(prog, loc, L, inv):
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

       # if any(map(lambda p: self.is_inv_loc(p.first()), self.stalepaths)) or\
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

        S = None  # safe states
        H = None  # negation of loop condition

        for u in unsafe:
            EM = u.getExprManager()
            S = unify_annotations(S or AssumeAnnotation(EM.getFalse(), {}, EM),
                                  state_to_annotation(u), EM)
            H = EM.Or(H or EM.getFalse(), u.getConstraints()[0])

        # FIXME: EM is out of scope
        # This is the first inductive set on H
        S = AssertAnnotation(EM.simplify(EM.And(EM.Not(S.getExpr()), H)),
                             S.getSubstitutions(), EM)
        seq = InductiveSequence(S)

        # FIXME: EM is out of scope
        print('--- starting executing ---')
        EM = getGlobalExprManager()
        while True:
            print('--- iter ---')
            print('Seq:\n', seq)

            if __debug__:
                r = seq.check_ind_on_paths(self, L.getPaths())
                assert r.errors is None, 'seq is not inductive'

            r = seq.check_on_paths(self, L.getPaths())
            # we could construct rule out the states that are in Serr.Not
            # manually, to speed-up the process...
            #r = exec_on_loop(loc, self, L, post=[Serr])
            if r.errors is None or r.ready is None:
                # no errors or all infeasible
                break

            newseq = abstract(self, L, r, seq)
            if newseq:
                seq = newseq
            else:
                # NOTE: we must use Not(r.errors), r.ready does not yield inductive set
                # for some reason (even with early and other empty)...
                # why? Why, oh, why?
                # NOTE 2 hmm, was probably a bug...
                # A = states_to_annotation(r.errors).Not(EM)
                seq.append(states_to_annotation(r.ready), None)

            print('New seq:\n', seq)
            S = seq.toannotation(True)
            if check_inv(self.getProgram(), loc, L, S):
                print_stdout(
                    f"{S} is invariant of loc {loc.getBBlock().getID()}",
                    color="BLUE")
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
