from copy import copy
from sys import stdout

from slowbeast.cfkind.annotatedcfg import CFGPath


class InductionPath:
    """
    An object that consists of a state and a CFG path.
    It is a helper class for performing efficient checks
    for reachable errors
    """

    def __init__(self, cfg, state, blocks=[]):
        self.cfg = cfg
        self.state = state
        self.path = CFGPath(blocks)

    def copy(self):
        return InductionPath(self.cfg, self.state.copy(), copy(self.path.locations()))

    def get_state(self):
        return self.state

    def get_path(self):
        return self.path

    def append_location(self, loc):
        self.path.append(loc)
        return self

    def reaches_assert(self):
        return self.path.reaches_assert()

    def extend(self):
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

    def dump(self, stream=stdout):
        stream.write("state: {0}\n".format(self.state.get_id()))
        stream.write("path: ")
        self.path.dump(stream)

    def __repr__(self):
        return "({0}):: {1}".format(self.state.get_id(), self.path)
