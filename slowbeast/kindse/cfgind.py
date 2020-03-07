from .. symexe.symbolicexecution import SEOptions
from .. util.debugging import print_stderr, print_stdout, dbg

from . annotatedcfg import CFG, CFGPath
from . basickindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from . basickindse import Result
from . inductionpath import InductionPath

from copy import copy

class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=SEOptions()):
        super(
            KindSymbolicExecutor, self).__init__(prog, opts)

        self.cfgs = {}
        self.paths = []

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def executePath(self, path, fromInit=False):
        if fromInit:
            if not self.states:
                self.prepare()
            states = self.states
            assert states
            print_stdout("Executing path from init: {0}".format(path), color="ORANGE")
            # we must execute without lazy memory
            executor = self.getExecutor()
        else:
            s = self.getIndExecutor().createState()
            s.pushCall(None, self.getProgram().getEntry())
            s.pc = path.first().getBBlock().first()
            states=[s]
            executor = self.getIndExecutor()

            print_stdout("Executing path: {0}".format(path), color="ORANGE")

        assert states

        ready, notready = executor.executePath(states, path)
        self.stats.paths += 1
        return ready, notready

    def extendPath(self, path, atmost=False):
        front = path.first()

        preds = front.getPredecessors()
        # FIXME: do not do this prepend, we always construct a new list....
        # rather do append and then execute in reverse order (do a reverse iterator)
        newpaths = [CFGPath([p] + path.getLocations()) for p in preds]

        if atmost and len(preds) == 0:
            assert len(newpaths) == 0
            newpaths.append(path)

        return newpaths

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

    def report(self, n):
        if n.hasError():
            print_stderr(
                "{0}: {1}, {2}".format(
                    n.getID(),
                    n.pc,
                    n.getError()),
                color='RED')
            self.stats.errors += 1
        elif n.wasKilled():
            print_stderr(
                n.getStatusDetail(),
                prefix='KILLED STATE: ',
                color='WINE')
            self.stats.killed_paths += 1

    def checkPaths(self):
        newpaths = []
        has_err = False

        for path in self.paths:
            # FIXME: use also the ready paths to constraint the state space
            # in the future

            first_loc = path.first()
            if self._is_init(first_loc):
                # try executing the path from initial states
                _, notready = self.executePath(path, fromInit=True)
                if not notready:
                    if len(first_loc.getPredecessors()) == 0:
                        # this path is safe and we do not need to prolong it
                        continue
                    # else just fall-through to execution from clear state
                    # as we can still prolong this path
                else:
                    for n in notready:
                        # we found a real error
                        if n.hasError():
                            self.report(n)
                            return Result.UNSAFE
                        if n.wasKilled():
                            self.report(n)
                            return Result.UNKNOWN

            _, notready = self.executePath(path)

            for n in notready:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path)
                    break
                if n.wasKilled():
                    self.report(n)
                    return Result.UNKNOWN

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

    def initializePaths(self, k = 1):
        paths = []
        cfg = self.getCFG(self.getProgram().getEntry())
        for n in cfg.getNodes():
            if n.hasAssert():
                paths.append(CFGPath([n]))
        while k > 0:
            paths = [np for p in paths for np in self.extendPath(p, atmost=True)]
            k -= 1
        return paths

    def run(self):
        dbg("Performing the k-ind algorithm only for the main function",
            color="ORANGE")

        k = 1

        self.paths = self.initializePaths()

        if len(self.paths) == 0:
            print_stdout("Found no error state!", color='GREEN')
            return 0

        while True:
            print_stdout("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r = self.checkPaths()
            if r is Result.SAFE:
                print_stdout("All possible error paths ruled out!", color="GREEN")
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

