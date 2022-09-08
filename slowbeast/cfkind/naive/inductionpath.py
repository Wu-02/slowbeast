from copy import copy
from sys import stdout

from slowbeast.cfkind.annotatedcfg import CFGPath
from typing import List, TextIO


class InductionPath:
    """
    An object that consists of a state and a CFG path.
    It is a helper class for performing efficient checks
    for reachable errors
    """

    def __init__(self, cfg, state, blocks=[]) -> None:
        self.cfg = cfg
        self.state = state
        self.path = CFGPath(blocks)

    def copy(self) -> "InductionPath":
        return InductionPath(self.cfg, self.state.copy(), copy(self.path.locations()))

    def get_state(self):
        return self.state

    def get_path(self) -> CFGPath:
        return self.path

    def append_location(self, loc) -> "InductionPath":
        self.path.append(loc)
        return self

    def reaches_assert(self):
        return self.path.reaches_assert()

    def extend(self) -> List[InductionPath]:
        last = self.path.last()
        if last:
            succs = last.successors()
        else:
            succs = [self.cfg.get_node(self.state.pc.bblock())]

        if len(succs) == 1:
            self.path.append(succs[0])
            return [self]
        else:
            return [self.copy().append_location(s) for s in succs]

    def has_successors_with_assert(self):
        last = self.path.last()
        if last:
            succs = last.successors()
        else:
            succs = [self.cfg.get_node(self.state.pc.bblock())]

        return [s for s in succs if s.has_assert()]

    def dump(self, stream: TextIO = stdout) -> None:
        stream.write(f"state: {self.state.get_id()}\n")
        stream.write("path: ")
        self.path.dump(stream)

    def __repr__(self) -> str:
        return f"({self.state.get_id()}):: {self.path}"
