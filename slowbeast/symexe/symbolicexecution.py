from .. interpreter.interpreter import Interpreter
from .. interpreter.errors import ExecutionError
from . executor import Executor as SExecutor
from . executionstate import SEState
from . memory import SymbolicMemory
from .. solvers.solver import Solver
from .. util.debugging import print_stderr, print_stdout, dbg


class Stats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.errors = 0
        self.instructions = 0


class SymbolicExecutor(Interpreter):
    def __init__(self, P, concretize_nondet=False):
        self.solver = Solver()
        super(SymbolicExecutor, self).__init__(P, SExecutor(self.solver, concretize_nondet))
        self.stats = Stats()

    def getInitialStates(self, entry):
        s = SEState(None, m=SymbolicMemory(self.solver))
        s.pushCall(None, entry)
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
            elif s.hasError():
                print_stderr("{0}: {1}, {2}".format(s.getID(), s.pc, s.getError()), color='RED')
                self.stats.errors += 1
                self.stats.paths += 1
            elif s.isTerminated():
                print_stderr(s.getError(), color='BROWN')
                self.stats.paths += 1
            else:
                assert s.exited()
                dbg("state exited with exitcode {0}".format(s.getExitCode()))
                self.stats.paths += 1
                self.stats.exited_paths += 1

    def run(self):
        self.states = self.getInitialStates(self.entry)

        try:
            while self.states:
                state = self.getNextState()
                newstates = self._executor.execute(state, state.pc)
                self.handleNewStates(newstates)
        except ExecutionError as e:
            print_stderr(
                "Fatal error while executing '{0}': {1}".format(
                    state.pc, str(e)), color='RED')
            state.dump()
            return -1
        except Exception as e:
            print_stderr("Fatal error while executing '{0}'".format(state.pc),
                         color='RED')
            state.dump()
            raise e

        return 0
