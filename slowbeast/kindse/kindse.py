from .. symexe.symbolicexecution import SymbolicExecutor, SEOptions
from .. symexe.executionstate import SEState
from .. symexe.memory import SymbolicMemory
from .. util.debugging import print_stderr, print_stdout, dbg

from . annotatedcfg import CFG, CFGPath

from copy import copy
from sys import stdout

class InductionPath:
    """
    An object that consists of a state and a CFG path.
    It is a helper class for performing efficient checks
    for reachable errors
    """

    def __init__(self, cfg, state, blocks = []):
        self.cfg = cfg
        self.state = state
        self.path = CFGPath(blocks)

    def copy(self):
        return InductionPath(self.cfg, self.state.copy(),
                             copy(self.path.getLocations()))

    def getState(self):
        return self.state

    def getPath(self):
        return self.path

    def appendLoc(self, loc):
        self.path.append(loc)
        return self

    def reachesAssert(self):
        return self.path.reachesAssert()

    def extend(self):
        last = self.path.last()
        if last:
            succs = last.getSuccessors()
        else:
            succs = [self.cfg.getNode(self.state.pc.getBBlock())]

        if len(succs) == 1:
            self.path.append(succs[0])
            return [self]
        else:
            return [self.copy().appendLoc(s) for s in succs]

    def successorsWithAssert(self):
        last = self.path.last()
        if last:
            succs = last.getSuccessors()
        else:
            succs = [self.cfg.getNode(self.state.pc.getBBlock())]

        return [s for s in succs if s.hasAssert()]

    def dump(self, stream=stdout):
        stream.write("state: {0}\n".format(self.state.getID()))
        stream.write("path: ")
        self.path.dump(stream)

    def __repr__(self):
        return "({0}):: {1}".format(self.state.getID(), self.path)

class KindSymbolicExecutor(SymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=SEOptions()):
        super(
            KindSymbolicExecutor, self).__init__(prog, opts)

        dbg("Forbidding calls for now with k-induction")
        self.getExecutor().forbidCalls()

        self.cfgs = {}

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def extendBase(self):
        states = self.getExecutor().executeTillBranch(self.base)
        self.base = []
        for ns in states:
            if ns.hasError():
                print_stderr(
                    "{0}: {1}, {2}".format(
                        ns.getID(),
                        ns.pc,
                        ns.getError()),
                    color='RED')
                self.stats.errors += 1
                self.stats.paths += 1
                return False
            elif ns.isReady():
                self.base.append(ns)
            elif ns.isTerminated():
                print_stderr(ns.getError(), color='BROWN')
                self.stats.paths += 1
                self.stats.terminated_paths += 1
            elif ns.wasKilled():
                self.stats.paths += 1
                self.stats.killed_paths += 1
                print_stderr(
                    ns.getStatusDetail(),
                    prefix='KILLED STATE: ',
                    color='WINE')
            else:
                assert ns.exited()
                self.stats.paths += 1
                self.stats.exited_paths += 1

        if not self.base:
            # no ready states -> we searched all the paths
            return True

        return None

    def executePath(self, path):
        dbg("Executing path: {0}".format(path), color="ORANGE")
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

    def run(self):
        self.prepare()

        dbg("Performing the k-ind algorithm only for the main function",
            color="ORANGE")

        k = 1
        self.base = self.states  # start from the initial states
        self.ind = self.initializeInduction()

        while True:
            print_stdout("-- starting iteration {0} --".format(k))

            dbg("Extending base".format(k), color="BLUE")
            r = self.extendBase()
            if r is False:
                dbg("Error found.", color='RED')
                return 1
            elif r is True:
                print_stdout("We searched the whole program!", color='GREEN')
                return 0

            dbg("Extending induction step".format(k), color="BLUE")
            if self.extendInd():
                print_stdout("Did not hit any possible error while building "\
                             "induction step!".format(k),
                    color="GREEN")
                return 0

            dbg("Checking induction step".format(k), color="BLUE")
            if self.checkInd():
                print_stdout("Induction step succeeded!", color='GREEN')
                return 0

            k += 1

