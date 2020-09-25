from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from . kindcfgpath import KindCFGPath
from . annotations import Relation, get_relations

from . kindsebase import KindSymbolicExecutor as BaseKindSE

def get_safe_inv_candidates(safe, unsafe):
    for s in safe:
        # get and filter out those relations that make the state safe
        saferels = (
            r for r in get_relations(s) if not all(
                u.is_sat(
                    r.expr) for u in unsafe))
        for x in saferels:
            yield x

def get_unsafe_inv_candidates(safe, unsafe):
    for s in unsafe:
        # get and filter out those relations that make the state safe
        # FIXME: isn't this superfluous in this case?
        for r in get_relations(s):
            yield r.neg(s.getExprManager()) 

def check_inv(prog, loc, r):
    dbg_sec(
        f"Checking if {r} is invariant of loc {loc.getBBlock().getID()}")
    
    kindse = BaseKindSE(prog)
    invpaths = []
    for p in loc.getPredecessors():
        apath = AnnotatedCFGPath([p])
        apath.addLocAnnotationBefore(r.toAssertion(), loc)
        invpaths.append(KindCFGPath(apath))
    
    dbg_sec("Running nested KindSE")
    res = kindse.run(invpaths, maxk=15)
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

        self.genannot = genannot
        self.invpoints = {}
 
    def getInv(self, loc, safe, unsafe):
        prog = self.getProgram()
        for r in get_safe_inv_candidates(safe, unsafe):
            if check_inv(prog, loc, r):
                print_stdout(
                    f"{r} is invariant of loc {loc.getBBlock().getID()}!",
                    color="BLUE")
                yield r
        for r in get_unsafe_inv_candidates(safe, unsafe):
            if check_inv(prog, loc, r):
                print_stdout(
                    f"{r} is invariant of loc {loc.getBBlock().getID()}!",
                    color="BLUE")
                yield r


    def annotateCFG(self, path, safe, unsafe):
        """
        Take the executed path and states that are safe and unsafe
        and derive annotations of CFG
        """
        if not self.genannot:  # we should not generate invariants
            return

        assert isinstance(path.cfgpath.first(), CFG.AnnotatedNode)
        cfgpath = path.cfgpath
        if not path.cfgpath.first() in self.invpoints[cfgpath[0].getCFG()]:
            return

        loc = path.cfgpath.first()
        for inv in self.getInv(loc, safe, unsafe):
            dbg(f"Adding {inv} as assumption to the CFG")
            loc.annotationsBefore.append(inv.toAssumption())

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
                elif r is Result.UNKNOWN:
                    # there is a problem with this path,
                    # but we can still find an error
                    # on some different path
                    # FIXME: keep it in queue so that
                    # we can rule out this path by
                    # annotations from other paths?
                    continue
                assert r is None, r

            safe, unsafe = self.executePath(cfgpath)

            self.annotateCFG(path, safe, unsafe)

            step = self.getOptions().step
            for n in unsafe:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path,
                                                steps=step,
                                                atmost=step != 1,
                                                stoppoints=self.invpoints[path[0].getCFG()])
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
        paths = []
        for F in self.getProgram().getFunctions():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            invpoints = self.findInvPoints(cfg)
            self.invpoints[cfg] = invpoints

            nodes = cfg.getNodes()
            npaths = [KindCFGPath(AnnotatedCFGPath([p])) for n in nodes
                      for p in n.getPredecessors()
                      if n.hasAssert()]
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
