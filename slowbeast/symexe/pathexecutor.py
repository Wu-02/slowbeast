from slowbeast.util.debugging import dbg, dbgv
from . executor import Executor as SExecutor


class Executor(SExecutor):
    """
    Symbolic Executor instance adjusted to executing
    paths with possibly annotated with formulas.
    """
    def __init__(self, solver, opts, memorymodel=None):
        super(Executor, self).__init__(solver, opts, memorymodel)


