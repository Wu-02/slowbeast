from .. symexe.symbolicexecution import SymbolicExecutor
#from . executor import Executor as SExecutor
#from . executionstate import SEState
#from . memory import SymbolicMemory
from .. solvers.solver import Solver
from .. util.debugging import print_stderr, print_stdout, dbg

class KindSymbolicExecutor(SymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            concretize_nondet=False,
            by_blocks=False,
            interactive=False):
        super(
            KindSymbolicExecutor, self).__init__(
            prog,
            concretize_nondet=concretize_nondet,
            by_blocks=by_blocks,
            interactive=interactive)

        print("Forbidding calls for now with k-induction")
        self.getExecutor().forbidCalls()

   #def getNextState(self):
   #    if not self.states:
   #        return None

   #    # DFS for now
   #    return self.states.pop()

   #def handleNewStates(self, newstates):
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
