from . executionstate import ExecutionState
from . executor import Executor
from . errors import ExecutionError

class Interpreter:
    def __init__(self, program, executor = Executor()):
        self._program = program
        self._executor = executor

        self._execs = ExecutionState(None)
        self._execs.pushCall(None, program.getEntry())

    def dump(self):
        assert self._execs
        self._execs.dump()

    def run(self):
        try:
            while self._execs.pc:
                self.step()
        except ExecutionError as e:
            print("Execution error while executing '{0}': {1}".format(self._execs.pc, str(e)))
            self.dump()
        except Exception as e:
            print("Fatal error while executing '{0}'".format(self._execs.pc))
            self.dump()
            raise e

        if self._execs.hasError():
            print("Error while executing '{0}'".format(self._execs))
            print(self._execs.getError())
            self.dump()
            return -1
        elif self._execs.exited():
            return self._execs.getExitCode()

        return None

    def step(self):
        """ execute the current instruction and modify the state accordingly """

        states = self._executor.execute(self._execs, self._execs.pc)
        assert len(states) == 1
        self._execs = states[0]

