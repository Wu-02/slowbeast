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

    def executePath(self, path):
        s = SEState(
            None,
            SymbolicMemory(
                self.getSolver(),
                uninit_nondet=True),
            self.getSolver())
        s.pushCall(None, self.getProgram().getEntry())
        s.pc = path.first().getBBlock().first()

        print_stdout("Executing path: {0}".format(path), color="ORANGE")
        self.getExecutor().setLazyMemAccess(True)
        ready, notready = self.getExecutor().executePath(s, path)
        self.getExecutor().setLazyMemAccess(False)

        return ready, notready

    def extendPath(self, path):
        front = path.first()
        newpaths = []

        preds = front.getPredecessors()
        # FIXME: do not do this prepend, we always construct a new list....
        # rather do append and then execute in reverse order (do a reverse iterator)
        for p in preds:
            newpaths.append(CFGPath([p] + path.getLocations()))

        return newpaths

    def checkPaths(self):
        newpaths = []
        has_err = False

        for path in self.paths:
            # FIXME: use also the ready paths to constraint the state space
            # in the future
            _, notready = self.executePath(path)
            self.stats.paths += 1

            for n in notready:
                if n.hasError():
                    has_err = True

                    if path.first().getBBlock() is\
                        self.getProgram().getEntry().getBBlock(0):
                        print_stderr(
                            "{0}: {1}, {2}".format(
                                n.getID(),
                                n.pc,
                                n.getError()),
                            color='RED')
                        self.stats.errors += 1
                        return False

                    newpaths += self.extendPath(path)
                    break

        self.paths = newpaths

        if not has_err:
            return True

        return None

    def initializePaths(self):
        paths = []
        cfg = self.getCFG(self.getProgram().getEntry())
        for n in cfg.getNodes():
            if n.hasAssert():
                paths.append(CFGPath([n]))
        return paths

    def run(self):
        self.prepare()

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




