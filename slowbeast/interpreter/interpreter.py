from . executionstate import ExecutionState
from . executor import Executor
from . errors import ExecutionError

class Interpreter:
    def __init__(self, program, dbg=False):
        self._program = program
        self._execs = ExecutionState(program.getEntry().getBBlock(0).getInstruction(0))
        self._executor = Executor(dbg)
        self._ec = None

    def dump(self):
        print("-- Interpreter state --")
        if not self._execs:
            print("No state")
            return
        print("-- Call stack:")
        self._execs.cs.dump()
        print("-- Memory:")
        self._execs.memory.dump()
        print("-- -- -- -- -- -- -- --")

    def run(self):
        try:
            while self._execs:
                self.step()
        except ExecutionError as e:
            print("Execution error while executing '{0}': {1}".format(self._execs.pc, str(e)))
            self.dump()
        except Exception as e:
            print("Fatal error while executing '{0}'".format(self._execs.pc))
            self.dump()
            raise e

        return self._ec

    def step(self):
        """ execute the current instruction and modify the state accordingly """

        self._ec = self._executor.execute(self._execs, self._execs.pc)

        if self._execs.pc is None: # we have no other instruction to continue
            self.dump()
            self._execs = None


