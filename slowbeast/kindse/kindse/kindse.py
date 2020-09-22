from slowbeast.util.debugging import print_stdout, dbg

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from . kindcfgpath import KindCFGPath
from . annotations import Relation, get_relations

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

        self.genannot = genannot
        self.invpoints = []

    def annotateCFG(self, path, safe, unsafe):
        """
        Take the executed path and states that are safe and unsafe
        and derive annotations of CFG
        """
        if not self.genannot:  # we should not generate invariants
            return

        if not path.cfgpath.first() in self.invpoints:
            return

        for s in safe:
            print("--Constraints--")
            print(s.getConstraints())
            print("--Relations--")

            # filter out those relations that make the state safe
            saferels = (
                r for r in get_relations(s) if not all(
                    u.is_sat(
                        r.expr) for u in unsafe))

            for r in saferels:
                kindse = BaseKindSE(self.getProgram())
                apath = AnnotatedCFGPath([path.cfgpath.first()])
                apath.addAnnotation(r.toAnnotation())
                paths=[KindCFGPath(apath)]
                res = kindse.run(paths, maxk=5)
                print(r, res)

    def checkInitialPath(self, path):
        """
        Execute a path from initial states
        \requires an initial path
        """

        cfgpath = path.cfgpath
        safe, unsafe = self.executePath(cfgpath, fromInit=True)
        if not unsafe:
            self.annotateCFG(path, safe, unsafe)
            if len(cfgpath.first().getPredecessors()) == 0:
                # this path is safe and we do not need to extend it
                return Result.SAFE
            # else just fall-through to execution from clear state
            # as we can still prolong this path
        else:
            for n in unsafe:
                # we found a real error or hit another problem
                if n.hasError() or n.wasKilled():
                    return self.report(n)
                else:
                    assert False, "Unhandled unsafe state"
        return None

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            cfgpath = path.cfgpath

            first_loc = cfgpath.first()
            if self._is_init(first_loc):
                r = self.checkInitialPath(path)
                if r is Result.UNSAFE:
                    return r  # found a real error
                elif r is Result.SAFE:
                    continue  # this path is safe
                assert r is None

            safe, unsafe = self.executePath(cfgpath)

            self.annotateCFG(path, safe, unsafe)

            step = self.getOptions().step
            for n in unsafe:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path,
                                                steps=step,
                                                atmost=step != 1,
                                                stoppoints=self.invpoints)
                    break
                elif n.wasKilled():
                    return self.report(n)
                else:
                    assert False, "Unhandled Unsafe state"

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

    def findInvPoints(self, cfg):
        points = []

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                points.append(end)

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        cfg = self.getCFG(self.getProgram().getEntry())

        self.invpoints = self.findInvPoints(cfg)

        nodes = cfg.getNodes()
        paths = [KindCFGPath(AnnotatedCFGPath([p])) for n in nodes
                 for p in n.getPredecessors()
                 if n.hasAssert()]
        step = self.getOptions().step
        while k > 0:
            paths = [
                np for p in paths for np in self.extendPath(
                    p, steps=step, atmost=True, stoppoints=self.invpoints)]
            k -= 1

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
            print_stdout("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r = self.checkPaths()
            if r is Result.SAFE:
                print_stdout(
                    "All possible error paths ruled out!",
                    color="GREEN")
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNSAFE:
                dbg("Error found.", color='RED')
                return 1
            elif r is Result.UNKNOWN:
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
