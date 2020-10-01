from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import InstrsAnnotation, AssumeAnnotation, AssertAnnotation

from . annotations import InvariantGenerator, execute_loop
from . kindsebase import KindSymbolicExecutor as BaseKindSE

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

        self.InvGen = InvariantGenerator
        self.genannot = genannot
        self.invpoints = {}
        self.invgenerators = {}
        self.have_problematic_path = False

    def getInv(self, loc, states):
        IG = self.invgenerators.setdefault(loc, self.InvGen(self.getProgram(), loc))

        for inv in IG.generate(states):
            yield inv

    def executeLoop(self, loc, states):
        # assert states are inductive on loc
        return execute_loop(self, loc, states)

    def annotateCFG(self, path, states):
        """
        Take the executed path and states that are safe and unsafe
        and derive annotations of CFG
        """
        if not self.genannot:  # we should not generate invariants
            return

        # FIXME: make CFG an attribute of path
        loc = path.first()
        assert isinstance(loc, CFG.AnnotatedNode)
        if not loc in self.invpoints[loc.getCFG()]:
            return

        dbg_sec(f"Executing loop from {loc.getBBlock().getID()}")
        self.executeLoop(loc, states)
        dbg_sec()
       #loc = path.first()
       #dbg_sec(f"Trying to generate annotations for {loc.getBBlock().getID()}")
       #for inv in self.getInv(loc, states):
       #    dbg(f"Adding {inv} as assumption to the CFG")
       #    for annot in inv:
       #        loc.annotationsBefore.append(annot)
       #dbg_sec()

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            first_loc = path.first()
            if self._is_init(first_loc):
                r, states = self.checkInitialPath(path)
                if r is Result.UNSAFE:
                    self.reportfn(f"Error path: {path}", color="RED")
                    return r, states  # found a real error
                elif r is Result.SAFE:
                    self.reportfn(f"Safe (init) path: {path}", color="DARK_GREEN")
                    continue  # this path is safe
                elif r is Result.UNKNOWN:
                    self.have_problematic_path = True
                    # there is a problem with this path,
                    # but we can still find an error
                    # on some different path
                    # FIXME: keep it in queue so that
                    # we can rule out this path by
                    # annotations from other paths?
                    continue
                assert r is None, r

            r = self.executePath(path)

            killed = (s for s in r.other if s.wasKilled()) if r.other else None
            if killed:
                self.have_problematic_path = True
                for s in killed:
                    self.report(s)

            self.annotateCFG(path, r)

            step = self.getOptions().step
            if r.errors:
                self.reportfn(f"Possibly error path: {path}", color="ORANGE")
                has_err = True
                newpaths += self.extendPath(path,
                                            steps=step,
                                            atmost=step != 1,
                                            stoppoints=self.invpoints[path[0].getCFG()])
            else:
                self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        self.paths = newpaths

        if not has_err:
            return Result.SAFE, None

        return None, None

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

    def run(self, paths=None, maxk=None):
        dbg("Performing the k-ind algorithm only for the main function",
            color="ORANGE")

        k = 1

        if paths:
            self.paths = paths
        else:
            self.paths = self.initializePaths()

        if len(self.paths) == 0:
            print_stdout("Found no error state!", color='GREEN')
            return 0

        while True:
            print_stdout(f"Starting iteration {k}")
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r, states = self.checkPaths()
            if r is Result.SAFE:
                if self.have_problematic_path:
                    print_stdout("Enumerating paths finished, but a problem was met.", color='ORANGE')
                    return 1

                print_stdout(
                    "All possible error paths ruled out!",
                    color="GREEN")
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNSAFE:
                for s in states:
                    self.report(s)
                print_stdout("Error found.", color='RED')
                return 1
            elif r is Result.UNKNOWN:
                for s in states:
                    self.report(s)
                print_stdout("Hit a problem, giving up.", color='ORANGE')
                return 1
            else:
                assert r is None

            k += 1
            if maxk and maxk <= k:
                print_stdout(
                    "Hit the maximal number of iterations, giving up.",
                    color='ORANGE')
                return 1
