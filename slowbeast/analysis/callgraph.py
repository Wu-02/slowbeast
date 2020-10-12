from .. ir.function import Function
from .. ir.instruction import Call

from sys import stdout
from copy import copy

class CallGraph:
    class Node:
        def __init__(self, F):
            __slots__ = ['fun', 'callsites', 'callers']
            self.fun = F
            self.callers = []
            self.callsites = {}

        def getFun(self):
            return self.fun

        def getCallSites(self):
            return self.callsites

        def getCallers(self):
            return self.callers

        def addCallSite(self, callsite, funs):
            self.callsites[callsite] = funs
            for f in funs:
                f.callers.append((self, callsite))

    __slots__ = ['program', '_nodes']

    def __init__(self, P):
        self.program = P
        self._nodes = {}

        self._build()

    def createNode(self, *args):
        """ Override this method in child classes
        to get nodes with more data
        """
        assert len(args) == 1
        return CallGraph.Node(*args)

    def getNode(self, B):
        return self._nodes.get(B)

    def getNodes(self):
        return self._nodes.values()

    def _build(self):
        for F in self.program.getFunctions():
            self._nodes[F] = self.createNode(F)

        for fun, node in self._nodes.items():
            self._build_fun(fun, node)

    def _build_fun(self, fun, node):
        for block in fun.getBBlocks():
            for I in block.getInstructions():
                if not isinstance(I, Call):
                    continue

                # FIXME: no function pointers yet
                node.addCallSite(I, [self._nodes[I.getCalledFunction()]])

    def dump(self, stream=stdout):
        for f, node in self._nodes.items():
            stream.write("Fun '{0}' calls\n".format(f.getName()))
            for cs, funs in node.getCallSites().items():
                for n, cf in enumerate(funs):
                    if n == 0:
                        stream.write("  {0} -> {1}\n".format(cs.getID(),
                                                             cf.getFun().getName()))
                    else:
                        stream.write(
                            "     -> {0}\n".format(cf.getFun().getName()))
