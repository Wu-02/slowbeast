from .. analysis.cfg import CFG as PureCFG
from .. analysis.cfg import CFGPath as PureCFGPath
from .. ir.instruction import Assert


class CFG(PureCFG):
    """
    CFG with nodes annotated with information
    about possible error sites and other
    useful information.
    """

    class AnnotatedNode(PureCFG.Node):
        __slots__ = ['_has_assert']

        def __init__(self, B):
            super(CFG.AnnotatedNode, self).__init__(B)
            # find out whether this node has an assert
            self._has_assert = False
            for i in B.getInstructions():
                if isinstance(i, Assert):
                    self._has_assert = True
                    break

        def hasAssert(self):
            return self._has_assert

    def __init__(self, F):
        super(CFG, self).__init__(F)

    def createNode(self, *args):
        assert len(args) == 1
        return CFG.AnnotatedNode(*args)


class CFGPath(PureCFGPath):
    def __init__(self, locs=[]):
        super(CFGPath, self).__init__(locs)

    def reachesAssert(self):
        if len(self.locations) <= 0:
            return False

        return self.locations[-1].hasAssert()
