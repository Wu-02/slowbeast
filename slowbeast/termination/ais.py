from typing import Optional, Sized, List, Type

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bse import report_state
from slowbeast.bse.bself import BSELF, BSELFChecker as BSELFCheckerVanilla
from slowbeast.bse.loopinfo import LoopInfo
from slowbeast.bse.options import BSELFOptions
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.symexe.annotations import Annotation, execute_annotation
from slowbeast.symexe.executionstate import SEState as ExecutionState
from slowbeast.symexe.memory import Memory
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.symbolicexecution import SymbolicExecutor, SEOptions, SExecutor
from slowbeast.util.debugging import (
    print_stdout,
    inc_print_indent,
    dec_print_indent,
    dbg,
)


#####################################################################
# Forward execution
#####################################################################


class ForwardState(ExecutionState):
    """
    Execution state of forward symbolic execution.
    It is exactly the same as the parent class, but it also
    computes the number of hits to a particular loop headers.
    """

    __slots__ = "_loc_visits"

    def __init__(
        self,
        executor=None,
        pc: Optional[Memory] = None,
        m: Optional[Memory] = None,
        solver=None,
        constraints=None,
    ) -> None:
        super().__init__(executor, pc, m, solver, constraints)
        self._loc_visits = {}

    def _copy_to(self, new: ExecutionState) -> None:
        super()._copy_to(new)
        # FIXME: use COW
        new._loc_visits = self._loc_visits.copy()

    def visited(self, inst) -> None:
        n = self._loc_visits.setdefault(inst, 0)
        self._loc_visits[inst] = n + 1

    def num_visits(self, inst=None):
        if inst is None:
            inst = self.pc
        return self._loc_visits.get(inst)


class ForwardExecutor(SExecutor):
    def create_state(self, pc=None, m=None) -> ForwardState:
        if m is None:
            m = self.get_memory_model().create_memory()
        s = ForwardState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s


class SeAIS(SymbolicExecutor):
    def __init__(
        self,
        program,
        ohandler=None,
        opts: SEOptions = SEOptions(),
    ) -> None:
        super().__init__(program, ohandler, opts, None, ForwardExecutor)
        programstructure = ProgramStructure(program, self.new_output_file)
        self.programstructure = programstructure
        self._loop_headers = {
            loc.elem()[0]: loc for loc in self.programstructure.get_loop_headers()
        }
        self.get_cfa = programstructure.cfas.get

    def is_loop_header(self, inst):
        return inst in self._loop_headers

    def _register_loop_states(self, state) -> None:
        n = state.num_visits()
        assert n > 0, "Bug in counting visits"
        states = self.forward_states.setdefault(state.pc, [])
        # if we have a state that visited state.pc n times,
        # we must have visited it also k times for all k < n
        assert len(states) != 0 or n == 1, self.forward_states
        assert len(states) >= n - 1, self.forward_states
        if len(states) == n - 1:
            states.append([state.copy()])
        else:
            assert len(states) >= n
            states[n - 1].append(state.copy())

    # S = self.executor().create_states_set(state)
    # loc = self._loop_headers[state.pc]
    # A, rels, states =\
    #   self.forward_states.setdefault(loc, (self.executor().create_states_set(), set(), []))
    # cur_rels = set()
    # for rel in (r for r in get_var_cmp_relations(state, A) if r not in rels):
    #    if rel.get_cannonical().is_concrete(): # True
    #        continue
    #    rels.add(rel)
    #    cur_rels.add(rel)
    #    print('rel', rel)
    #    A.add(S)
    # states.append((state, rels))
    # print(states)
    # print(A)


#####################################################################
# Backward execution
#####################################################################


class BSELFChecker(BSELFCheckerVanilla):
    def __init__(
        self,
        loc,
        A,
        program,
        programstructure: Optional[ProgramStructure],
        opts: BSELFOptions,
        invariants=None,
        indsets=None,
        max_loop_hits=None,
        forward_states=None,
    ) -> None:
        super().__init__(
            loc, A, program, programstructure, opts, invariants, indsets, max_loop_hits
        )
        self.forward_states = forward_states
        memorymodel = LazySymbolicMemoryModel(opts)
        pathexecutor = PathExecutor(program, self.solver(), opts, memorymodel)
        # forbid defined calls...
        # pathexecutor.forbid_calls()
        self._pathexecutor = pathexecutor

    def check_loop_precondition(self, L, A: Annotation):
        loc = L.header()
        print_stdout(f"Checking if {str(A)} holds on {loc}", color="purple")

        # "fast" path -- check with the forward states that we have
        fstates = self.forward_states.get(L.header().elem()[0])
        if fstates:
            # use only the states from entering the loop -- those are most
            # likely to work
            states = [s.copy() for s in fstates[0]]
            _, n = execute_annotation(self._pathexecutor, states, A)
            if n and any(map(lambda s: s.has_error(), n)):
                return Result.UNKNOWN, None
        inc_print_indent()
        # run recursively BSELFChecker with already computed inductive sets
        checker = BSELFChecker(
            loc,
            A,
            self.program,
            self.programstructure,
            self.options,
            indsets=self.inductive_sets,
            invariants=self.invariant_sets,
            max_loop_hits=1,
            forward_states=self.forward_states,
        )
        result, states = checker.check(L.entries())

        dec_print_indent()
        dbg(f"Checking if {A} holds on {loc} finished")
        return result, states

    def fold_loop(self, loc, L: LoopInfo, unsafe: Sized, loop_hit_no: int) -> bool:
        fstates = self.forward_states.get(L.header().elem()[0])
        if fstates is None:
            self.max_seq_len = 2
        else:
            self.max_seq_len = 2  # * len(L.paths())
        return super().fold_loop(loc, L, unsafe, loop_hit_no)

    def do_step(self):
        bsectx = self.get_next_state()
        if bsectx is None:
            return (
                Result.UNKNOWN if self.problematic_states else Result.SAFE
            ), self.problematic_paths_as_result()
        return self._do_step(bsectx)
