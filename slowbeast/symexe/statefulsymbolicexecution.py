from .executor import Executor as SExecutor
from ..util.debugging import print_stderr, print_stdout, dbg

from . symbolicexecution import SEOptions, SymbolicExecutor


class StatefulSymbolicExecutor(SymbolicExecutor):
    def __init__(
        self, P, ohandler=None, opts=SEOptions(), executor=None, ExecutorClass=SExecutor
    ):
        super().__init__(
            P, ohandler, opts, executor, ExecutorClass,
        )
        self._seen_states = []

    def handleNewState(self, state):
        if state.isReady() and not self.is_subsumed(state):
            self.states.append(state)
        else:
            super().handleNewState(state)

    def is_subsumed(self, state):
        """
        Return true if we have a state that was implied by this state
        """
        return True