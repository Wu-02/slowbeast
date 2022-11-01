from typing import Optional, Sized
from random import randint

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bself import BSELFChecker as BSELFCheckerVanilla
from slowbeast.bse.loopinfo import LoopInfo
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.symexe.annotations import Annotation, execute_annotation
from slowbeast.symexe.executionstate import SEState as ExecutionState
from slowbeast.symexe.memory import Memory
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.symbolicexecution import SymbolicExecutor, SEOptions, SExecutor
from slowbeast.termination.memorymodel import AisSymbolicMemoryModel
from slowbeast.core.errors import NonTerminationError
from slowbeast.util.debugging import (
    print_stdout,
    print_stderr,
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

    def start_tracing_memory(self):
        self.memory.start_tracing()

    def stop_tracing_memory(self):
        self.memory.stop_tracing()


class ForwardExecutor(SExecutor):
    def __init__(
            self,
            program,
            solver,
            opts: SEOptions,
            memorymodel = None,
    ) -> None:
        super().__init__(program, solver, opts,
                         memorymodel=memorymodel or AisSymbolicMemoryModel(opts))

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
        self._loop_exits = {loc.target().elem()[0] for loc in self.programstructure.get_loop_exits() }
        self.get_cfa = programstructure.cfas.get
        self._loop_entry_states = {}

    def _is_loop_header(self, inst):
        return inst in self._loop_headers

    def _exited_loop(self, inst):
        return inst in self._loop_exits

    def _states_may_be_same(self, state, prev):
            assert state.pc == prev.pc
            meml, memr = prev.memory, state.memory

            # we're comparing states in different contexts...
            assert len(meml._cs) == len(memr._cs)

            check = []
            expr_mgr = state.expr_manager()
            for reg, mo_l in meml._objects.items():
                mo_r = memr._objects.get(reg)
                if mo_r is None:
                    return False
                # compare the two memory objects value by value
                for mid, lval in mo_l._values.items():
                    rval = mo_r._values.get(mid)
                    if rval is None:
                        # TODO: if we take uninitialized memory as non-deterministic,
                        # we should assume that in this case the values may be the same
                        return False
                    expr = expr_mgr.Eq(lval, rval)
                    if expr.is_concrete() and not expr.value():
                        return False
                    check.append(expr)
            return state.is_sat(expr_mgr.conjunction(*check))

    def _already_visited(self, state):
        S = self._loop_entry_states.get(state.pc)
        if S is None:
            return False
        states_may_be_same = self._states_may_be_same
        for prev_states in S.values():
            for prev in prev_states:
                if states_may_be_same(state, prev):
                    return True
        return False

    def _handle_state_space_cycle(self, s: ForwardState) -> None:
        testgen = self.ohandler.testgen if self.ohandler else None
        opts = self.get_options()
        stats = self.stats
        if s.has_error() and opts.replay_errors:
            assert not opts.threads, opts
            print_stdout("Found an error, trying to replay it", color="white")
            inc_print_indent()
            repls = self.replay_state(s)
            dec_print_indent()
            if not repls or not repls.has_error():
                print_stderr("Failed replaying error", color="orange")
                s.set_killed("Failed replaying error")
            else:
                dbg("The replay succeeded.")
        if s.has_error():
            if not opts.replay_errors:
                dbgloc = s.pc.get_metadata("dbgloc")
                if dbgloc:
                    print_stderr(
                        f"[{s.get_id()}] {dbgloc[0]}:{dbgloc[1]}:{dbgloc[2]}: {s.get_error()}",
                        color="redul",
                    )
                else:
                    print_stderr(
                        f"{s.get_id()}: {s.get_error()} @ {s.pc}",
                        color="redul",
                    )
                print_stderr("Error found.", color="red")
            # else: we already printed this message

            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.process_state(s)
            if opts.exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return

    def handle_new_state(self, state: ForwardState) -> None:
        pc = state.pc

        if self._already_visited(state):
            state.set_error(NonTerminationError("an infinite execution found"))
            self._handle_state_space_cycle(state)
            return

        if state.is_ready():
            if self._is_loop_header(pc):
                state.visited(pc)
                self._add_loop_state(state)
           #    state.start_tracing_memory()
           #elif self._exited_loop(pc):
           #    state.stop_tracing_memory()
        super().handle_new_state(state)


    def _add_loop_state(self, state) -> None:
        n = state.num_visits()
        assert n > 0, "Bug in counting visits"
        states = self._loop_entry_states.setdefault(state.pc, {})
        # if we have a state that visited state.pc n times,
        # we must have visited it also k times for all k < n
        assert len(states) != 0 or n == 1, self._loop_entry_states
        assert len(states) >= n - 1, self._loop_entry_states
        states.setdefault(n-1, []).append(state.copy())

    def get_next_state(self):
        states = self.states
        if not states:
            return None
       ## take the state from the middle of the list
       #l = len(states)
       #if l > 2:
       #    states[int(l/2)], states[-1] =  states[-1], states[int(l/2)]

        # move random state in the queue at the end of queue so that we pop it
        pick = randint(0, len(states)-1)
        states[pick], states[-1] =  states[-1], states[pick]
        state = states.pop()
        assert state.get_id() not in (
            st.get_id() for st in self.states
        ), f"State already in queue: {state} ... {self.states}"
        return state

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
        opts,
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
