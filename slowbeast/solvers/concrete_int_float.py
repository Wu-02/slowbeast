from slowbeast.domains.exprmgr import ExpressionManager
from slowbeast.solvers.solver import SolverIntf


class ConcreteSolver(SolverIntf):
    """
    Just check for True/False values of concrete computation
    wrapped to the interface solver.
    """

    def __init__(self, em: ExpressionManager = ExpressionManager()) -> None:
        super().__init__(em)

    def is_sat(self, *e) -> bool:
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))

    def try_is_sat(self, timeout, *e) -> bool:
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))
