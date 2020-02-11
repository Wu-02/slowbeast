from .. symexe.symbolicexecution import SymbolicExecutor, SEOptions
#from . executor import Executor as SExecutor
#from . memory import SymbolicMemory
#from .. solvers.solver import Solver
from .. symexe.executionstate import SEState
from .. symexe.memory import SymbolicMemory
from .. util.debugging import print_stderr, print_stdout, dbg


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
                return True
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

        return False

    def extendInd(self):
        self.getExecutor().setLazyMemAccess(True)

        states = self.getExecutor().executeTillBranch(self.ind)
        self.ind = []
        found_err = False
        for ns in states:
            if ns.hasError():
                found_err = True
                dbg("Hit error state while building IS assumptions: {0}: {1}, {2}".format(
                    ns.getID(), ns.pc, ns.getError()))
            elif ns.isReady():
                self.ind.append(ns)
            elif ns.isTerminated():
                print_stderr(ns.getError(), color='BROWN')
            elif ns.wasKilled():
                print_stderr(
                    ns.getStatusDetail(),
                    prefix='KILLED STATE: ',
                    color='WINE')
            else:
                assert ns.exited()

        self.getExecutor().setLazyMemAccess(False)
        return not found_err

    def checkInd(self):
        self.getExecutor().setLazyMemAccess(True)

        frontier = [s.copy() for s in self.ind]
        states = self.getExecutor().executeTillBranch(frontier)
        has_error = False
        for ns in states:
            if ns.hasError():
                has_error = True
                dbg("Induction check hit error state: {0}: {1}, {2}".format(
                    ns.getID(), ns.pc, ns.getError()))
                break
           # elif ns.isTerminated():
           #    print_stderr(ns.getError(), color='BROWN')
           # elif ns.wasKilled():
           #    print_stderr(
           #        ns.getStatusDetail(),
           #        prefix='KILLED STATE: ',
           #        color='WINE')

        self.getExecutor().setLazyMemAccess(False)
        return not has_error

    def run(self):
        self.prepare()

        k = 1
        self.base = self.states  # start from the initial states
        dbg("Performing the algorithm only for the main function")
        self.ind = []
        for b in self.getProgram().getEntry().getBBlocks():
            s = SEState(
                None,
                SymbolicMemory(
                    self.getSolver(),
                    uninit_nondet=True),
                self.getSolver())
            s.pushCall(None, self.getProgram().getEntry())
            s.pc = b.first()
            self.ind.append(s)

        while True:
            dbg("-- starting iteration {0} --".format(k))

            dbg("Extending base".format(k))
            if self.extendBase():
                return 1

            dbg("Extending induction step".format(k))
            if self.extendInd():
                return 0

            dbg("Checking induction step".format(k))
            if self.checkInd():
                dbg("Induction step succeeded!", color='GREEN')
                return 0

            k += 1

   # def getNextState(self):
   #    if not self.states:
   #        return None

   #    # DFS for now
   #    return self.states.pop()

   # def handleNewStates(self, newstates):
   #    self.stats.instructions += 1
   #    for s in newstates:
   #        if s.isReady():
   #            self.states.append(s)
   #        elif s.hasError():
   #            print_stderr(
   #                "{0}: {1}, {2}".format(
   #                    s.getID(),
   #                    s.pc,
   #                    s.getError()),
   #                color='RED')
   #            self.stats.errors += 1
   #            self.stats.paths += 1
   #            if self.testgen:
   #                self.testgen.processState(s)
   #        elif s.isTerminated():
   #            print_stderr(s.getError(), color='BROWN')
   #            self.stats.paths += 1
   #            self.stats.terminated_paths += 1
   #            if self.testgen:
   #                self.testgen.processState(s)
   #        elif s.wasKilled():
   #            self.stats.paths += 1
   #            self.stats.killed_paths += 1
   #            print_stderr(
   #                s.getStatusDetail(),
   #                prefix='KILLED STATE: ',
   #                color='WINE')
   #            if self.testgen:
   #                self.testgen.processState(s)
   #        else:
   #            assert s.exited()
   #            dbg("state exited with exitcode {0}".format(s.getExitCode()))
   #            self.stats.paths += 1
   #            self.stats.exited_paths += 1
   #            if self.testgen:
   #                self.testgen.processState(s)
