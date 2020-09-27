from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import InstrsAnnotation, AssumeAnnotation, AssertAnnotation

from . annotations import Relation, get_relations

from . kindsebase import KindSymbolicExecutor as BaseKindSE

def get_safe_inv_candidates(safe, unsafe):
    for s in safe:
        # get and filter out those relations that make the state safe
        saferels = (
            r for r in get_relations(s) if not all(
                u.is_sat(r[0]) for u in unsafe))
        for x in saferels:
            yield x

def get_unsafe_inv_candidates(unsafe):
    for s in unsafe:
        # get and filter out those relations that make the state safe
        # FIXME: isn't this superfluous in this case?
        EM = s.getExprManager()
        for r in get_relations(s):
            yield EM.Not(r[0]), r[1]

def get_inv_candidates(states):
    errs = states.errors
    ready = states.ready
    if ready and errs:
        for r in get_safe_inv_candidates(ready, errs):
            yield r
    if errs:
        for r in get_unsafe_inv_candidates(errs):
            yield r
    if states.other:
        for r in get_safe_inv_candidates((s for s in states.other if s.isTerminated()), errs):
            yield r

def check_inv(prog, loc, inv):
    expr, subs = inv
    dbg_sec(
        f"Checking if {expr} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"  > {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    annot = AssertAnnotation(expr, subs)

    apath = AnnotatedCFGPath([loc])
    apath.addLocAnnotationBefore(annot, loc)

    dbg_sec("Running nested KindSE")
    res = kindse.run([apath], maxk=8)
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
        self.tested_invs = {}
        self.have_problematic_path = False

    def getInv(self, loc, states):
        locid = loc.getBBlock().getID()
        prog = self.getProgram()
        for inv in get_inv_candidates(states):
           #if r in self.tested_invs.setdefault(locid, set()):
           #    continue
           #self.tested_invs[locid].add(r)

            print_stdout(f'Checking if {inv[0]} is invariant for {locid}')
            if check_inv(prog, loc, inv):
                print_stdout(
                    f"{inv[0]} is invariant of loc {locid}!",
                    color="BLUE")
                yield inv

    def annotateCFG(self, path, states):
        """
        Take the executed path and states that are safe and unsafe
        and derive annotations of CFG
        """
        if not self.genannot:  # we should not generate invariants
            return

        # FIXME: make CFG an attribute of path
        assert isinstance(path.first(), CFG.AnnotatedNode)
        if not path[0] in self.invpoints[path[0].getCFG()]:
            return

        loc = path.first()
        dbg_sec(f"Trying to generate annotations for {loc.getBBlock().getID()}")
        for inv in self.getInv(loc, states):
            dbg(f"Adding {inv[0]} as assumption to the CFG")
            loc.annotationsBefore.append(AssumeAnnotation(inv[0], inv[1]))
        dbg_sec()

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
                    self.reportfn(f"Safe path: {path}", color="DARK_GREEN")
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
