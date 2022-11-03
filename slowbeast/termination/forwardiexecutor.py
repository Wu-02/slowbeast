from typing import Optional

from slowbeast.symexe.executionstate import SEState as ExecutionState
from slowbeast.symexe.iexecutor import IExecutor
from slowbeast.symexe.memory import Memory
from slowbeast.symexe.options import SEOptions
from slowbeast.termination.memorymodel import AisSymbolicMemoryModel
from slowbeast.util.cowlist import COWList


class ForwardState(ExecutionState):
    """
    Execution state of forward symbolic execution.
    It is exactly the same as the parent class, but it also
    computes the number of hits to a particular loop headers.
    """

    __slots__ = "_loc_visits", "_loop_entry_states", "_loop_entry_states_ro"

    def __init__(
        self,
        executor=None,
        pc: Optional[Memory] = None,
        m: Optional[Memory] = None,
        solver=None,
        constraints=None,
    ) -> None:
        super().__init__(executor, pc, m, solver, constraints)
        # mapping from loop entry instruction to memory projections
        self._loop_entry_states = {}
        self._loop_entry_states_ro = False

    def _copy_to(self, new: ExecutionState) -> None:
        super()._copy_to(new)
        new._loop_entry_states = self._loop_entry_states
        new._loop_entry_states_ro = self._loop_entry_states_ro = True

    def entry_loop(self, proj) -> None:
        if self._loop_entry_states_ro:
            self._loop_entry_states = {
                pc: states.copy() for pc, states in self._loop_entry_states.items()
            }
            self._loop_entry_states_ro = False

        states = self._loop_entry_states
        pc = self.pc
        states.setdefault(pc, COWList()).append(proj)

    def get_loop_entry_states(self, pc):
        r = self._loop_entry_states.get(pc)
        if r:
            return r
        return None


class ForwardIExecutor(IExecutor):
    def __init__(
        self,
        program,
        solver,
        opts: SEOptions,
        memorymodel=None,
    ) -> None:
        super().__init__(
            program,
            solver,
            opts,
            memorymodel=memorymodel or AisSymbolicMemoryModel(opts),
        )

    def create_state(self, pc=None, m=None) -> ForwardState:
        if m is None:
            m = self.get_memory_model().create_memory()
        s = ForwardState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s
