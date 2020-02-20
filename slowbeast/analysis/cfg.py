from .. ir.function import Function
from .. ir.instruction import Branch

from sys import stdout
from copy import copy

class CFG:
    class Node:
        def __init__(self, B):
            self.block = B
            self.successors = []
            self.predecessors = []

        def getBBlock(self):
            return self.block

        def getSuccessors(self):
            return self.successors

        def getPredecessors(self):
            return self.predecessors

        def addSuccessor(self, succ):
            for s in self.successors:
                if s == succ:
                    return

            self.successors.append(succ)
            succ.predecessors.append(self)


    def __init__(self, F):
        self.fun = F
        self._nodes = {}

        self._build()

    def createNode(self, *args):
        """ Override this method in child classes
        to get nodes with more data
        """
        assert len(args) == 1
        return CFG.Node(*args)

    def getNode(self, B):
        return self._nodes.get(B)

    def _build(self):
        for B in self.fun.getBBlocks():
            self._nodes[B] = self.createNode(B)

        for block, node in self._nodes.items():
            br = block.last()
            if not isinstance(br, Branch):
                continue

            node.addSuccessor(self._nodes[br.getTrueSuccessor()])
            node.addSuccessor(self._nodes[br.getFalseSuccessor()])

    def dump(self, stream=stdout):
        for node in self._nodes.values():
            for succ in node.getSuccessors():
                stream.write("{0} -> {1}\n".format(node.getBBlock().getID(),
                                                   succ.getBBlock().getID()))

class CFGPath:
    def __init__(self, locs=None):
        if locs:
            self.locations = locs
        else:
            self.locations = []

    def __len__(self):
        return len(self.locations)

    def copy(self):
        return copy(self)

    def append(self, l):
        self.locations.append(l)

    def first(self):
        if len(self.locations) == 0:
            return None
        return self.locations[0]

    def last(self):
        if len(self.locations) == 0:
            return None
        return self.locations[-1]

    def endswith(self, path):
        if len(self) < len(path):
            return False

        if len(path) == 0:
            return True

        pl = len(path) - 1
        sl = len(self) - 1
        for idx in range(0, len(path)):
            if path.locations[pl - idx] != self.locations[sl - idx]:
                return False
        return True

    def getLocations(self):
        return self.locations

    def dump(self, stream=stdout):
        stream.write(self)
        stream.write('\n')

    def __repr__(self):
        return  " -> ".join(map(lambda x: str(x.getBBlock().getID()), self.locations))

