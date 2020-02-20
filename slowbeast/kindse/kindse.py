from .. symexe.symbolicexecution import SEOptions
from .. symexe.executionstate import SEState
from .. symexe.memory import SymbolicMemory
from .. util.debugging import print_stderr, print_stdout, dbg

from . annotatedcfg import CFG
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

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def executePath(self, path):
        print_stdout("Executing path: {0}".format(path), color="ORANGE")
        self.getExecutor().setLazyMemAccess(True)
        ready, notready = self.getExecutor().executePath(path)
        self.getExecutor().setLazyMemAccess(False)

        return ready, notready

    def extendIndPath(self, path):
        newpaths = []
        found_err = False

        for p in path.extend():
            if not p.reachesAssert():
                newpaths.append(p)
                continue

            # this path may reach an assert
            # so we must really execute it and get those
            # states that do no violate the assert
            ready, notready = self.executePath(p)

            for r in ready:
                newpaths.append(InductionPath(r))

            for ns in notready:
                if ns.hasError():
                    found_err = True
                    dbg("Hit error state while building IS assumptions: {0}: {1}, {2}".format(
                        ns.getID(), ns.pc, ns.getError()),
                        color="PURPLE")
           #    elif ns.isTerminated():
           #        print_stderr(ns.getError(), color='BROWN')
           #    elif ns.wasKilled():
           #        print_stderr(
           #            ns.getStatusDetail(),
           #            prefix='KILLED STATE: ',
           #            color='WINE')
           #    else:
           #        assert ns.exited()

        return newpaths, found_err

    def extendInd(self):
        found_err = False
        newpaths = []
        for path in self.ind:
            tmp, f_err = self.extendIndPath(path)
            newpaths += tmp
            found_err |= f_err

        self.ind = newpaths

        return not found_err

    def checkInd(self):
        for path in self.ind:
            for succ in path.successorsWithAssert():
                dbg("Can reach assert in one step: {0}".format(path))
                ready, notready = self.executePath(path.copy().appendLoc(succ))

                for ns in notready:
                    if ns.hasError():
                        dbg("Induction check hit error state: {0}: {1}, {2}".format(
                            ns.getID(), ns.pc, ns.getError()),
                            color="PURPLE")
                        return False
        return True

    def initializeInduction(self):
        ind = []
        cfg = self.getCFG(self.getProgram().getEntry())
        for b in self.getProgram().getEntry().getBBlocks():
            s = SEState(
                None,
                SymbolicMemory(
                    self.getSolver(),
                    uninit_nondet=True),
                self.getSolver())
            s.pushCall(None, self.getProgram().getEntry())
            s.pc = b.first()

            ind.append(InductionPath(cfg, s))
        return ind

