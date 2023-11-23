from typing import Optional

from slowbeast.symexe.iexecutor import IExecutor
from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.ir.program import Program
from slowbeast.symexe.state import SEState
from slowbeast.util.channel import Channel

from .interpreter import SymbolicInterpreter
from .options import SEOptions
from slowbeast.ir.instruction import Load


def get_loads(state):
    vals = state.memory.get_cs().values_list()
    for v in vals:
        if isinstance(v, Load):
            val = state.memory.get(v)
            if val.is_pointer():
                continue
            conc = state.concretize(val)
            if conc is not None:
                yield (v, conc[0])


def serialize_state(state):
    vals = (f"{i} = {v}" for (i, v) in ((i.get_id(), v) for (i, v) in get_loads(state)))
    return f"reach: {state.pc.get_id()}: {', '.join(vals)}".encode()


class CooperativeSymbolicInterpreter(SymbolicInterpreter):
    """
    SymbolicInterpreter that shares information about what it does
    and what it found out.
    """

    def __init__(
        self,
        P: Program,
        channels,
        ohandler=None,
        opts: SEOptions = SEOptions(),
        executor: Optional[IExecutor] = None,
        ExecutorClass=IExecutor,
        programstructure=None,
    ) -> None:
        super().__init__(P, ohandler, opts, executor, ExecutorClass)

        if programstructure is None:
            programstructure = ProgramStructure(P, self.new_output_file)
        self.programstructure = programstructure
        assert len(channels) == 1, "Support only one channel right now"
        self.channels = [Channel(chan) for chan in channels]

        self._loop_headers = {
            loc.elem()[0]: loc for loc in self.programstructure.get_loop_headers()
        }

    def _is_loop_header(self, inst):
        return inst in self._loop_headers

    def handle_new_state(self, state: SEState) -> None:
        super().handle_new_state(state)

        if self.channels and self._is_loop_header(state.pc):
            if not self.channels[0].send(serialize_state(state)):
                # channel closed
                self.channels.pop(0)
