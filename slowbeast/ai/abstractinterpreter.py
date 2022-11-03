from slowbeast.symexe.interpreter import SEOptions
from .executor import IExecutor as AIExecutor
from ..interpreter.interpreter import Interpreter
from ..util.debugging import print_stderr, dbg
from io import TextIOWrapper
from typing import Optional, Sized, Type
from slowbeast.ir.program import Program
from slowbeast.symexe.iexecutor import IExecutor


class AIOptions(SEOptions):
    pass


class AIStats:
    def __init__(self) -> None:
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0


class AbstractInterpreter(Interpreter):
    def __init__(
        self,
        P: Program,
        ohandler=None,
        opts: AIOptions = AIOptions(),
        executor: Optional[IExecutor] = None,
        ExecutorClass: Type[slowbeast.ai.executor.ForwardExecutor] = AIExecutor,
    ) -> None:
        super().__init__(P, opts, executor or ExecutorClass(opts))
        self.stats = AIStats()
        # outputs handler
        self.ohandler = ohandler
        self.explored_states = {}

    def new_output_file(self, name) -> TextIOWrapper:
        odir = self.ohandler.outdir if self.ohandler else None
        return open(f"{odir or '.'}/{name}", "w")

    def get_next_state(self):
        states = self.states
        if not states:
            return None

        # DFS for now
        return states.pop()

    def handle_new_states(self, newstates: Sized) -> None:
        hs = self.handle_new_state
        for s in newstates:
            hs(s)

    def handle_new_state(self, s) -> None:
        pc = s.pc
        if s in self.explored_states.setdefault(pc, set()):
            dbg("Already have this state")
            # if s.has_error():
            #    s.dump()
            #    print('---- HAVE ----')
            #    for x in self.explored_states[s.pc]:
            #        if x == s:
            #            x.dump()
            return
        self.explored_states[pc].add(s)

        testgen = self.ohandler.testgen if self.ohandler else None
        stats = self.stats
        if s.is_ready():
            self.states.append(s)
        elif s.has_error():
            print_stderr(f"{s.get_id()}: {s.pc}, {s.get_error()}", color="RED")
            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.process_state(s)
            if self.get_options().exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return
        elif s.is_terminated():
            print_stderr(s.get_error(), color="BROWN")
            stats.paths += 1
            stats.terminated_paths += 1
            if testgen:
                testgen.process_state(s)
        elif s.was_killed():
            stats.paths += 1
            stats.killed_paths += 1
            print_stderr(s.status_detail(), prefix="KILLED STATE: ", color="WINE")
            if testgen:
                testgen.process_state(s)
        else:
            assert s.exited()
            dbg(f"state exited with exitcode {s.get_exit_code()}")
            stats.paths += 1
            stats.exited_paths += 1
            if testgen:
                testgen.process_state(s)

    def report(self) -> None:
        pass

    # expl = self.explored_states
    # for pc, S in expl.items():
    #    pc.dump()
    #    print(' --- states ---')
    #    for s in S:
    #        s.dump()
    #    print(' --- all states ---')
