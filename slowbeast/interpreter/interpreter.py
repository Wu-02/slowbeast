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
        s = self.states.pop()
        assert len(self.states) == 0
        return s

    def handleNewStates(self, newstates):
        assert len(newstates) == 1,\
               "Concrete execution returned more than one state"

        state = newstates[0]
        if state.isReady():
            assert(len(self.states) == 0)
            self.states.append(state)
        elif state.hasError():
            print_stderr("Error while executing '{0}'".format(state),
                         color='RED')
            print_stderr(state.getError(), color='BROWN')
            state.dump()
        elif s.isTerminated():
            print_stderr(s.getError(), color='BROWN')
        elif s.wasKilled():
            print_stderr(
                s.getStatusDetail(),
                prefix='KILLED STATE: ',
                color='WINE')
        else:
            assert s.exited()
            dbg("state exited with exitcode {0}".format(s.getExitCode()))

        raise RuntimeError("This line should be unreachable")

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

