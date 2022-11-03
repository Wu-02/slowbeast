from random import randint
from typing import Optional, Sized

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bself import BSELFChecker as BSELFCheckerVanilla
from slowbeast.bse.loopinfo import LoopInfo
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.core.errors import NonTerminationError
from slowbeast.solvers.symcrete import IncrementalSolver
from slowbeast.symexe.annotations import Annotation, execute_annotation
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.symexe.pathexecutor import PathExecutor
from slowbeast.symexe.interpreter import SymbolicInterpreter, SEOptions
from slowbeast.termination.forwardiexecutor import ForwardState, ForwardIExecutor
from slowbeast.termination.memoryprojection import MemoryProjection
from slowbeast.util.debugging import (
    print_stdout,
    print_stderr,
    inc_print_indent,
    dec_print_indent,
    dbg,
)


def find_loop_body_entries(programstructure):
    """
    Find the first instruction from each loop body
    """

    headers = programstructure.get_loop_headers()
    ret = {}
    # go from the header until we find the assume edges
    for h in headers:
        node = h
        while not node.is_branching():
            node = node.get_single_successor_loc()
            if node == h:
                raise NotImplementedError("Unconditional loops not handled")
        if len(node.successors()) != 2 or any(
            (not e.is_assume() for e in node.successors())
        ):
            raise NotImplementedError("Unhandled structure of the loop")

        entry_edge = (
            node.successors()[0]
            if node.successors()[0].assume_true()
            else node.successors()[1]
        )
        assert entry_edge.assume_true(), entry_edge
        if len(entry_edge.elems()) != 1:
            raise NotImplementedError("Unhandled structure of the loop")

        following_edge = entry_edge.target().get_single_successor()
        if following_edge is None:
            raise NotImplementedError("Unhandled structure of the loop")
        if len(following_edge.elems()) < 1:
            raise NotImplementedError("Unhandled structure of the loop")

        entry_inst = following_edge.elems()[0]
        assert entry_inst not in ret, f"{entry_inst} in {ret}"
        ret[entry_inst] = h

    return ret


class SeAIS(SymbolicInterpreter):
    def __init__(
        self,
        program,
        ohandler=None,
        opts: SEOptions = SEOptions(),
    ) -> None:
        super().__init__(program, ohandler, opts, None, ForwardIExecutor)
        programstructure = ProgramStructure(program, self.new_output_file)
        self.programstructure = programstructure
        self._loop_body_entries = find_loop_body_entries(programstructure)

        self.get_cfa = programstructure.cfas.get
        self.projections_solver = IncrementalSolver()

    def _is_loop_entry(self, inst):
        return inst in self._loop_body_entries

    def _projections_may_be_same(self, solver, expr_mgr, cur_proj, prev_proj):
        # print('PREV', prev_proj)
        # print('NOW ', cur_proj)

        for (mo_id, offset), val in cur_proj.items():
            # compare the two memory objects value by value
            prevval = prev_proj.get(mo_id, offset)
            if prevval is None:
                # TODO: if we take uninitialized memory as non-deterministic,
                # we should assume that in this case the values may be the same
                return False
            expr = expr_mgr.Eq(val, prevval)
            if expr.is_concrete():
                if not expr.value():
                    return False
            else:
                solver.add(expr)
        return solver.is_sat()

    def _get_and_check_projection(self, state):
        mem_proj = MemoryProjection(state)
        S = state.get_loop_entry_states(state.pc)
        if not S:
            return mem_proj

        expr_mgr = state.expr_manager()
        solver = self.projections_solver
        solver.push()

        solver.add(state.constraints_obj().as_formula(expr_mgr))
        projections_may_be_same = self._projections_may_be_same

        for prev_md in S:
            solver.push()
            same = projections_may_be_same(solver, expr_mgr, mem_proj, prev_md)
            solver.pop()
            if same:
                solver.pop()
                return None
        solver.pop()
        return mem_proj

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

        if self._is_loop_entry(pc):
            assert state.is_ready()
            new_mp = self._get_and_check_projection(state)
            if new_mp is None:
                state.set_error(NonTerminationError("an infinite execution found"))
                self._handle_state_space_cycle(state)
                return

            state.entry_loop(new_mp)
        #    state.start_tracing_memory()
        # elif self._exited_loop(pc):
        #    state.stop_tracing_memory()
        if state.has_error():
            dbg("Discarding an error state (it is not non-termination)")
            return
        super().handle_new_state(state)

    def get_next_state(self):
        states = self.states
        if not states:
            return None
        ## take the state from the middle of the list
        # l = len(states)
        # if l > 2:
        #    states[int(l/2)], states[-1] =  states[-1], states[int(l/2)]

        # move random state in the queue at the end of queue so that we pop it
        pick = randint(0, len(states) - 1)
        states[pick], states[-1] = states[-1], states[pick]
        state = states.pop()
        assert state.get_id() not in (
            st.get_id() for st in self.states
        ), f"State already in queue: {state} ... {self.states}"
        return state

    # S = self.executor().create_states_set(state)
    # loc = self._loop_body_entries[state.pc]
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
