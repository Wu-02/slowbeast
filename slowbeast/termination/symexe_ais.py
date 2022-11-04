from random import randint

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.core.errors import NonTerminationError
from slowbeast.solvers.symcrete import IncrementalSolver
from slowbeast.symexe.interpreter import SymbolicInterpreter, SEOptions
from slowbeast.termination.forwardiexecutor import ForwardState, ForwardIExecutor
from slowbeast.termination.memoryprojection import MemoryProjection
from slowbeast.termination.ais import AisInference
from slowbeast.util.debugging import (
    print_stdout,
    print_stderr,
    inc_print_indent,
    dec_print_indent,
    dbg,
    dbgv,
    warn_once,
    FIXME,
)


def find_loop_body_entries(programstructure):
    """
    Find the first instruction from each loop body. Note that these instructions do not
    precisely correspond to loop headers in the backward analysis.
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

        # find the first instruction in the body of the loop. It is either on regular edge
        # or on an assume edge that has no ops, but corresponds to an instruction.
        following_edge = entry_edge.target().get_single_successor()
        if following_edge is None:
            raise NotImplementedError("Unhandled structure of the loop")
        while (len(following_edge.elems()) == 0) and (not following_edge.is_assume()):
            following_edge = following_edge.target().get_single_successor()
            if following_edge is None:
                raise NotImplementedError("Unhandled structure of the loop")
            if following_edge.source() == h:
                raise NotImplementedError("Unhandled structure of the loop")

        if following_edge.is_assume():
            entry_inst = following_edge.orig_elem()
        else:
            entry_inst = following_edge.elems()[0]
        assert entry_inst not in ret, f"{entry_inst} in {ret}"
        ret[entry_inst] = h

    return ret


class SeAISForward(SymbolicInterpreter):
    """
    The forward part of symbolic execution with acyclic inductive sets inference.
    """

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
            if self.handle_loop_entry(state):
                return

        if state.has_error():
            dbg("Discarding an error state (it is not non-termination)")
            return
        super().handle_new_state(state)

    def handle_loop_entry(self, state):
        assert state.is_ready()
        new_mp = self._get_and_check_projection(state)
        if new_mp is None:
            state.set_error(NonTerminationError("an infinite execution found"))
            self._handle_state_space_cycle(state)
            return True

        state.entry_loop(new_mp)
        return False

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


class SeAIS(SeAISForward):
    """
    Symbolic execution with acyclic inductive sets inference.
    """

    def __init__(
        self,
        program,
        ohandler=None,
        opts: SEOptions = SEOptions(),
    ) -> None:
        super().__init__(program, ohandler, opts)

        # self.get_loop_headers = self.programstructure.get_loop_headers
        self._loop_headers = {
            loc.elem()[0]: loc for loc in self.programstructure.get_loop_headers()
        }
        self._ais = {}

    def _is_loop_header(self, inst):
        return inst in self._loop_headers

    def _get_ais(self, pc):
        if pc not in self._ais:
            self._ais[pc] = AisInference(
                self._loop_headers[pc],
                self.get_program(),
                self.programstructure,
                self.get_options(),
                invariants=None,
                indsets=None,
                max_loop_hits=None,
            )
        return self._ais[pc]

    def handle_new_state(self, state: ForwardState) -> None:
        if self._is_loop_header(state.pc):
            ais = self._get_ais(state.pc)
            if self._state_is_subsumed(ais, state):
                dbg("State is subsumed, dropping it")
                return

            ais.do_step()
        super().handle_new_state(state)

    def _state_is_subsumed(self, ais, state):
        if len(self._loop_headers) > 1:
            # FIXME: we need to prove that reachable loops terminate or get theri AISs
            # FIXME: and check the subsumption w.r.t those (their WP at the loop actually)
            warn_once(
                self._state_is_subsumed,
                f"Cannot subsume state because of multiple loops",
            )
            return False
        FIXME(
            "We must check that all values from all_states exist in state, because the memory is not lazy."
        )
        # FIXME cnt: or we must create an annotation from the state that captures also memory -- we will need that
        # anyway at some point
        if ais.aistree.all_states.contains(state):
            return True
        print("======================")
        return False
