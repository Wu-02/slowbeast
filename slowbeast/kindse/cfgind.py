from .. symexe.symbolicexecution import SEOptions
from .. symexe.executionstate import SEState
from .. symexe.memory import SymbolicMemory
from .. util.debugging import print_stderr, print_stdout, dbg

from . annotatedcfg import CFG, CFGPath
from . basickindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
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
            states=self.states
            if not states:
                self.prepare()
            assert states
            print_stdout("Executing path from init: {0}".format(path), color="ORANGE")
        else:
            s = SEState(
                None,
                SymbolicMemory(
                    self.getSolver(),
                    uninit_nondet=True),
                self.getSolver())
            s.pushCall(None, self.getProgram().getEntry())
            s.pc = path.first().getBBlock().first()
            states=[s]

            print_stdout("Executing path: {0}".format(path), color="ORANGE")

        assert states

        self.getExecutor().setLazyMemAccess(True)
        ready, notready = self.getExecutor().executePath(states, path)
        self.getExecutor().setLazyMemAccess(False)

        self.stats.paths += 1

        return ready, notready

    def extendPath(self, path, atmost=False):
        front = path.first()
        newpaths = []

        preds = front.getPredecessors()
        # FIXME: do not do this prepend, we always construct a new list....
        # rather do append and then execute in reverse order (do a reverse iterator)
        for p in preds:
            newpaths.append(CFGPath([p] + path.getLocations()))

        if atmost and len(preds) == 0:
            assert len(newpaths) == 0
            newpaths.append(path)

        return newpaths

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

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
                            print_stderr(
                                "{0}: {1}, {2}".format(
                                    n.getID(),
                                    n.pc,
                                    n.getError()),
                                color='RED')
                            self.stats.errors += 1
                            return False

            _, notready = self.executePath(path)

            for n in notready:
                if n.hasError():
                    has_err = True

                    newpaths += self.extendPath(path)
                    break

        self.paths = newpaths

        if not has_err:
            return True

        return None

    def initializePaths(self, k = 1):
        paths = []
        cfg = self.getCFG(self.getProgram().getEntry())
        for n in cfg.getNodes():
            if n.hasAssert():
                paths.append(CFGPath([n]))
        while k > 0:
            extended = []
            for p in paths:
                extended += self.extendPath(p, atmost=True)
            paths = extended
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
            if r is True:
                print_stdout("All possible error paths ruled out!", color="GREEN")
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is False:
                return 1
            else:
                assert r is None

            k += 1




