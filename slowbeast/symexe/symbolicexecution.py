from .. interpreter.interpreter import Interpreter
from .. interpreter.errors import ExecutionError
from . executor import Executor as SExecutor
from . executionstate import SEState
from .. solvers.solver import Solver
from .. util.debugging import print_stderr, print_stdout, dbg


class Stats:
    def __init__(self):
        self.queued = 0
        self.paths = 0
        self.errors = 0
        self.instructions = 0

class SymbolicExecutor(Interpreter):
    def __init__(self, P):
        self.solver = Solver()
        super(SymbolicExecutor, self).__init__(P, SExecutor(self.solver))

        self.stats = Stats()

    def getInitialStates(self, entry):
        s = SEState()
        s.setPathCondition(self.solver.getExprManager().getTrue())
        s.pushCall(None, entry)
        self.stats.queued += 1
        return [s]

    def getNextState(self):
        if not self.states:
            return None

        # DFS for now
        return self.states.pop()

    def handleNewStates(self, newstates):
        self.stats.instructions += 1
        for s in newstates:
            if s.isReady():
                self.states.append(s)
                self.stats.queued += 1
            elif s.hasError():
                print_stderr(state.getError(), color='BROWN')
                self.stats.errors += 1
                self.stats.paths += 1
            else:
                assert s.exited()
                dbg("state exited with exitcode {0}".format(s.getExitCode()))
                self.stats.paths += 1


    def run(self):
        self.states = self.getInitialStates(self.entry)

        try:
            while self.states:
                state = self.getNextState()
                newstates = self._executor.execute(state, state.pc)
                self.handleNewStates(newstates)
        except ExecutionError as e:
            print_stderr(
                "Execution error while executing '{0}': {1}".format(
                    state, str(e)), color='RED')
            state.dump()
            return -1
        except Exception as e:
            print_stderr("Fatal error while executing '{0}'".format(state.pc),
                         color='RED')
            state.dump()
            raise e

        print_stdout("Queued states: {0}".format(self.stats.queued), color='CYAN')
        print_stdout("Executed instructions: {0}".format(self.stats.instructions), color='CYAN')
        print_stdout("Executed paths: {0}".format(self.stats.paths), color='CYAN')
        print_stdout("Executed branches: {0}".format(self._executor.stats.branchings), color='CYAN')
        print_stdout("Executed forks: {0}".format(self._executor.stats.forks), color='CYAN')
        print_stdout("Found errors: {0}".format(self.stats.errors), color='CYAN')

        return 0

