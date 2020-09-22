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

class AnnotatedCFGPath(CFGPath):
    """
    A CFG path that contains annotations.
    These annotations can put assumptions
    on values or similar. The annotations
    are a special set of instructions that
    are executed on given places.
    """

    def __init__(self, locs=[]):
        super(AnnotatedCFGPath, self).__init__(locs)
        self.annotations={}
        self.assertions={}

    def addAnnotation(self, annot, idx=0):
        """
        Add annotation to the given location on the path.
        The annotation should be evaluated "before"
        executing the location.
        For that reason, we allow also annotation
        that goes "after" the last block.
        """
        assert idx <= self.length()

        self.annotations.setdefault(idx, []).append(annot)

    def getAnnotations(self, idx):
        return self.annotations.get(idx) or []

    def addAssertions(self, annot, idx=0):
        """
        Add annotation to the given location on the path.
        The assertion should be evaluated "before"
        executing the location but after evaluating
        the annotations.
        For that reason, we allow also assertion
        that goes "after" the last block.
        """
        assert idx <= self.length()

        self.assertions.setdefault(idx, []).append(annot)

    def getAssertions(self, idx):
        return self.assertions.get(idx) or []

    def copyandprepend(self, loc):
        # FIXME: this is not efficient...
        n = AnnotatedCFGPath([loc] + self.getLocations())
        n.annotations = self.annotations
        return n


