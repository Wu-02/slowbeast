from ..ir.function import Function
from ..ir.instruction import Branch

from sys import stdout
from copy import copy


class CFG:
    class Node:
        __slots__ = ["_cfg", "_block", "_successors", "_predecessors"]

        def __init__(self, cfg, B):
            self._cfg = cfg
            self._block = B
            self._successors = []
            self._predecessors = []

        def getBBlock(self):
            return self._block

        def getSuccessors(self):
            return self._successors

        def getPredecessors(self):
            return self._predecessors

        def addSuccessor(self, succ):
            for s in self._successors:
                if s == succ:
                    return

            self._successors.append(succ)
            succ._predecessors.append(self)

        def getCFG(self):
            return self._cfg

        def isJoin(self):
            "This bblock Has several predecessors"
            return len(self._predecessors) > 1

        def isBranch(self):
            "This bblock Has several successors"
            return len(self._successors) > 1

    def __init__(self, F):
        self._fun = F
        self._entry = None
        self._nodes = {}

        self._build()

    def fun(self):
        return self._fun

    def createNode(self, *args):
        """Override this method in child classes
        to get nodes with more data
        """
        assert len(args) == 1
        return CFG.Node(self, *args)

    def getNode(self, B):
        return self._nodes.get(B)

    def getNodes(self):
        return self._nodes.values()

    def entry(self):
        assert self._entry, "Entry has not been set"
        return self._entry

    def set_entry(self, n):
        if not isinstance(n, CFG.Node):
            n = self.getNode(n)

        assert hasattr(n, "getSuccessors")
        self._entry = n

    def _build(self):
        fun = self._fun

        for B in fun.getBBlocks():
            self._nodes[B] = self.createNode(B)

        for block, node in self._nodes.items():
            br = block.last()
            if not isinstance(br, Branch):
                continue

            node.addSuccessor(self._nodes[br.getTrueSuccessor()])
            node.addSuccessor(self._nodes[br.getFalseSuccessor()])

        # the entry should be the first bblock in the function
        entrybb = fun.getBBlock(0)
        assert self.getNode(entrybb)
        self.set_entry(entrybb)

    def dump(self, stream=stdout):
        for node in self._nodes.values():
            for succ in node.getSuccessors():
                stream.write(
                    "{0} -> {1}\n".format(
                        node.getBBlock().get_id(), succ.getBBlock().get_id()
                    )
                )


class CFGPath:
    def __init__(self, locs=None):
        if locs:
            assert isinstance(locs, list)
            assert all(map(lambda x: isinstance(x, CFG.Node), locs))
            self.locations = locs
        else:
            self.locations = []

    def __len__(self):
        return len(self.locations)

    def __getitem__(self, idx):
        assert idx < len(self.locations)
        return self.locations[idx]

    def __iter__(self):
        return self.locations.__iter__()

    def copy(self):
        return copy(self)

    def subpath(start, end):
        n = copy(self)
        n.locations = self.locations[start:end]

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

    def length(self):
        return len(self.locations)

    def dump(self, stream=stdout):
        stream.write(str(self))
        stream.write("\n")

    def __repr__(self):
        return " -> ".join(map(lambda x: str(x.getBBlock().get_id()), self.locations))
