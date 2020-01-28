from .. interpreter.interpreter import Interpreter
from . executor import Executor as SExecutor
from . executionstate import SEState
from .. solvers.solver import Solver

class SymbolicExecutor(Interpreter):
    def __init__(self, P):
        self.solver = Solver()
        super(SymbolicExecutor, self).__init__(P, SExecutor(self.solver))

    def getInitialStates(self, entry):
        s = SEState(None)
        s.pushCall(None, entry)
        return [s]

    def getNextState(self):
        if not self.states:
            return None

        # DFS for now
        s = self.states[-1]
        self.states.pop()
        return s



