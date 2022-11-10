from random import randint

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.core.errors import NonTerminationError
from slowbeast.solvers.symcrete import IncrementalSolver
from slowbeast.symexe.interpreter import SymbolicInterpreter, SEOptions
from slowbeast.termination.ais import AisInference
from slowbeast.termination.forwardiexecutor import ForwardState, ForwardIExecutor
from slowbeast.termination.memoryprojection import MemoryProjection
from slowbeast.util.debugging import (
    print_stdout,
    print_stderr,
    inc_print_indent,
    dec_print_indent,
    dbg,
    warn_once,
    FIXME,
)


def find_first_inst_on_path(path):
    """
    Find first inst inside the loop on a given path.
    This instruction is the one that is after the first
    assume edge (the jump into the body).
    """
    edgeit = (edge for edge in path)

    # find first assume edge
    first_assume = None
    for edge in edgeit:
        if edge.is_assume():
            first_assume = edge
            break

    if first_assume is None:
        assert sum((1 if e.is_assume() else 0 for e in path)) == 0, path
        raise RuntimeError(f"Unhandled loop path, no assume edge found: {path}")

    # find the first edge that has some elements or the next assume edge
    # because the assume edge corresponds to a branch instruction
    elems = None
    for edge in edgeit:
        assert edge.elems() is not None  # the code relies on this
        elems = edge.elems()
        if elems:
            break
        if edge.is_assume():
            elems = [edge.orig_elem()]
            break

    if elems is None:
        # If elems is None it means that the loop above did no iteration
        # and therefore there is no next edge.
        # If there is no next edge, it means that the first assume edge
        # that we've found is also the jump to the header and the
        # only instruction on this path is the jump. Get the jump then,
        # which is not in elems() but it is the orig_elem().
        assert sum((1 if e.is_assume() else 0 for e in path)) == 1, path
        elems = [first_assume.orig_elem()]

    if not elems:
        raise RuntimeError(f"Unhandled loop path {path}")
    return elems[0]


def find_loop_body_entries(programstructure):
    """
    Find the first instruction from each loop body. Note that these instructions do not
    precisely correspond to loop headers in the backward analysis.
    """
    ret = {}

    loops = programstructure.get_loops()
    for header, loop in loops.items():
        if not loop:
            FIXME(f"Have no info about loop {header}, probably is not simple")
            continue
        for path in loop.paths():
            first_inst = find_first_inst_on_path(path)
            ret[first_inst] = header

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
            if val.is_pointer():
                assert prevval.is_pointer(), prevval
                expr = expr_mgr.And(
                    expr_mgr.Eq(val.object(), prevval.object()),
                    expr_mgr.Eq(val.offset(), prevval.offset()),
                )
            else:
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
            ais = AisInference(
                self._loop_headers[pc],
                self.get_program(),
                self.programstructure,
                self.get_options(),
                invariants=None,
                indsets=None,
                max_loop_hits=None,
            )
            if ais.aistree is None:
                ais = None  # creating initial AIS failed
            self._ais[pc] = ais
        return self._ais[pc]

    def handle_new_state(self, state: ForwardState) -> None:
        if self._is_loop_header(state.pc):
            ais = self._get_ais(state.pc)
            if ais is not None:
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
