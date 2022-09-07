from slowbeast.domains.symcrete import SymcreteDomain
from slowbeast.solvers.solver import SolverIntf


class ConcreteSolver(SolverIntf):
    """
    Just check for True/False values of concrete computation
    wrapped to the interface solver.
    """

    def __init__(self, em=SymcreteDomain()):
        super().__init__(em)

    def is_sat(self, *e):
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))

    # for x in e:
    #    assert x.is_bool()
    #    assert isinstance(x.value(), bool)
    #    if x.value() is False:
    #        return False
    # return True

    def try_is_sat(self, timeout, *e):
        assert all(map(lambda x: x.is_bool() and isinstance(x.value(), bool), e)), e
        return all(map(lambda x: x.value(), e))
