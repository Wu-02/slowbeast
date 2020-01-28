from .. interpreter.interpreter import Interpreter
from . executor import Executor as SExecutor
from .. solvers.solver import Solver

class SymbolicExecutor(Interpreter):
    def __init__(self, P):
        self.solver = Solver()
        super(SymbolicExecutor, self).__init__(P, SExecutor(self.solver))

