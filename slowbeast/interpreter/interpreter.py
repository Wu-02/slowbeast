from .. util.debugging import print_stderr
from . executionstate import ExecutionState
from . executor import Executor
from . errors import ExecutionError


class Interpreter:
    def __init__(self, program, executor=Executor()):
        self._program = program
        self._executor = executor

        self.entry = program.getEntry()
        self.states = []

    def getInitialStates(self, entry):
        """
        Get state(s) from which to start execution.
        May be overriden by child classes
        """
        s = ExecutionState(None)
        s.pushCall(None, entry)
        return [s]

    def getNextState(self):
        if not self.states:
            return None

        # this is concrete execution
        assert len(self.states) == 1
        s = self.states[-1]
        self.states.pop()
        return s

    def run(self):
        self.states = self.getInitialStates(self.entry)
        try:
            state = self.getNextState()
            while state:
                self.step(state)
                state = self.getNextState()
        except ExecutionError as e:
            print_stderr(
                "Execution error while executing '{0}': {1}".format(
                    state, str(e)), color='RED')
            state.dump()
        except Exception as e:
            print_stderr("Fatal error while executing '{0}'".format(state.pc),
                         color='RED')
            state.dump()
            raise e

        if state.hasError():
            print_stderr("Error while executing '{0}'".format(state),
                         color='RED')
            print_stderr(state.getError(), color='BROWN')
            state.dump()
            return -1
        elif state.exited():
            return state.getExitCode()

        return None

    def step(self, state):
        """ execute the current instruction and modify the state accordingly """
        states = self._executor.execute(state, state.pc)
        assert len(states) == 1
        self.states += states
