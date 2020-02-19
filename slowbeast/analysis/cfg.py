from .. ir.function import Function
from .. ir.instruction import Branch
from sys import stdout

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

    def _build(self):
        for B in self.fun.getBBlocks():
            self._nodes[B] = CFG.Node(B)

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

