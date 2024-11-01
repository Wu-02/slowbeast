from slowbeast.core.state import ExecutionState
from slowbeast.domains.concrete_value import ConcreteVal

# from slowbeast.domains.sign import ZODomain
from slowbeast.domains.signul import SignULDomain as Domain


class AbstractState(ExecutionState):
    """State of abstract interpretation"""

    # FIXME: move this to the super class?
    __slots__ = (
        "_executor",
        "_id",
    )
    _states_counter = 0

    def __init__(self, executor, pc, m):
        super().__init__(pc, m)

        AbstractState._states_counter += 1
        self._id = AbstractState._states_counter

        self._executor = executor

    def get_id(self):
        return self._id

    def is_sat(self, *e):
        return Domain.may_be_true(Domain.conjunction(*e))

    def eval(self, v):
        if isinstance(v, ConcreteVal):
            return Domain.lift(v)
        value = self.get(v)
        if value is None:
            raise RuntimeError(f"Use of uninitialized/unknown variable {v}")
        return value

    def is_feasible(self):
        """
        Solve the PC and return True if it is sat. Handy in the cases
        when the state is constructed manually.
        """
        return True

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = AbstractState(self._executor, self.pc, self.memory)
        super()._copy_to(new)  # cow copy of super class

        return new

    def concretize(self, *e):
        return (Domain.concretize(x) for x in e)

    def nondets(self):
        return ()

    def __hash__(self):
        return self.memory.__hash__() ^ hash(self.pc) ^ hash(self.status)
