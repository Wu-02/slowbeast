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
        self._infeasibleSuffixes = []

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def hasInfeasibleSuffix(self, path):
        for p in self._infeasibleSuffixes:
            if path.getPath().endswith(p):
                return True
        return False

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

            if self.hasInfeasibleSuffix(p):
                # FIXME: this works only for "assert False" as it is in its own block...
                dbg("Skipping path with infeasible suffix: {0}".format(p))
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
                    dbg("Hit error state in induction check: {0}: {1}, {2}".format(
                         ns.getID(), ns.pc, ns.getError()),
                         color="PURPLE")

            if len(notready) == 0 and len(ready) == 0:
                self._infeasibleSuffixes.append(p.getPath())

        return newpaths, found_err

    def extendPaths(self, ind):
        found_err = False
        newpaths = []
        for path in ind:
            tmp, f_err = self.extendIndPath(path)
            newpaths += tmp
            found_err |= f_err

        return newpaths, not found_err

    def extendInd(self):
        pass # we do all the work in checkInd

    def checkInd(self):
        self.ind, safe = self.extendPaths(self.ind)
        return safe

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

        # we do the first extension here, so that we can do the rest of the
        # work in checkInd and do not execute the paths repeatedly
        return self.extendPaths(ind)

