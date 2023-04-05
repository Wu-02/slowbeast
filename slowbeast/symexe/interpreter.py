from typing import Optional, Sized

from slowbeast.interpreter.interpreter import Interpreter
from slowbeast.ir.program import Program
from slowbeast.solvers.symcrete import SymbolicSolver, Solver
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.iexecutor import IExecutor
from slowbeast.util.debugging import (
    inc_print_indent,
    dec_print_indent,
)
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from .options import SEOptions
from .stats import SEStats


class SymbolicInterpreter(Interpreter):
    """
    Symbolic execution of programs. According to most of the literature,
    the name should be 'SymbolicExecutor', but we call it SymbolicInterpreter
    to follow the distinction between executor and interpreter in this project
    (the first one is for executing instructions or sequences of instructions
    and the latter for executing (interpreting) whole programs).
    """

    def __init__(
        self,
        P: Program,
        ohandler=None,
        opts: SEOptions = SEOptions(),
        executor: Optional[IExecutor] = None,
        ExecutorClass=IExecutor,
    ) -> None:
        self._solver = Solver()
        super().__init__(P, opts, executor or ExecutorClass(P, self._solver, opts))
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler
        self._input_vector = None

        if ohandler:
            self.new_output_file = self.ohandler.new_output_file
        else:
            from slowbeast.util.debugging import new_output_file

            self.new_output_file = new_output_file

    def set_input_vector(self, ivec) -> None:
        self._executor.set_input_vector(ivec)

    def solver(self) -> SymbolicSolver:
        return self._solver

    def get_next_state(self) -> SEState:
        states = self.states
        if not states:
            return None
        # DFS for now
        state = states.pop()
        assert state.get_id() not in (
            st.get_id() for st in self.states
        ), f"State already in queue: {state} ... {self.states}"
        return state

    def handle_new_states(self, newstates: Sized) -> None:
        hs = self.handle_new_state
        for s in newstates:
            hs(s)

    def handle_new_state(self, state: SEState) -> None:
        testgen = self.ohandler.testgen if self.ohandler else None
        opts = self.get_options()
        stats = self.stats
        if state.has_error() and opts.replay_errors and not opts.threads:
            print_stdout("Found an error, trying to replay it", color="white")
            inc_print_indent()
            repls = self.replay_state(state)
            dec_print_indent()
            if not repls or not repls.has_error():
                print_stderr("Failed replaying error", color="orange")
                state.set_killed("Failed replaying error")
            else:
                dbg("The replay succeeded.")

        if state.is_ready():
            # assert s.get_id() not in (
            #    st.get_id() for st in self.states
            # ), f"State already in queue: {s} ... {self.states}"
            self.states.append(state)
        elif state.has_error():
            if not opts.replay_errors:
                dbgloc = state.pc.get_metadata("dbgloc")
                if dbgloc:
                    print_stderr(
                        f"[{state.get_id()}] {dbgloc[0]}:{dbgloc[1]}:{dbgloc[2]}: {state.get_error()}",
                        color="redul",
                    )
                else:
                    print_stderr(
                        f"{state.get_id()}: {state.get_error()} @ {state.pc}",
                        color="redul",
                    )
                print_stderr("Error found.", color="red")
            # else: we already printed this message

            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.process_state(state)
            if opts.exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return
        elif state.is_terminated():
            print_stderr(state.get_error(), color="BROWN")
            stats.paths += 1
            stats.terminated_paths += 1
            if testgen:
                testgen.process_state(state)
        elif state.is_killed():
            stats.paths += 1
            stats.killed_paths += 1
            print_stderr(state.status_detail(), prefix="KILLED STATE: ", color="WINE")
            if testgen:
                testgen.process_state(state)
        else:
            assert state.exited()
            # dbg(f"state exited with exitcode {s.get_exit_code()}")
            stats.paths += 1
            stats.exited_paths += 1
            if testgen:
                testgen.process_state(state)

    def replay_state(self, state):
        ivec = state.input_vector()
        dbg(f"Input vector: {ivec}")

        class GatherStates:
            class Handler:
                def __init__(self):
                    self.states = []

                def process_state(self, s):
                    self.states.append(s)

            def __init__(self):
                self.testgen = GatherStates.Handler()
                self.states = self.testgen.states

        opts = SEOptions(self.get_options())
        opts.replay_errors = False
        handler = GatherStates()
        SE = SymbolicInterpreter(self.get_program(), handler, opts)
        SE.set_input_vector(ivec)
        SE.run()
        if len(handler.states) != 1:
            return None
        return handler.states[0]
