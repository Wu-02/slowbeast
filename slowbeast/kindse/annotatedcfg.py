from .. analysis.cfg import CFG as PureCFG
from .. analysis.cfg import CFGPath as PureCFGPath
from .. ir.instruction import Assert

from copy import deepcopy


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

    class AnnotatedLoc:
        def __init__(self, loc):
            assert isinstance(loc, CFG.AnnotatedNode), loc
            self.loc = loc
            # after loc execution
            self.annotationsAfter = [] 
            self.assertionsAfter = []
            # before loc execution
            self.annotationsBefore = []
            self.assertionsBefore = []

        def getPredecessors(self):
            return self.loc.getPredecessors()

        def getBBlock(self):
            return self.loc.getBBlock()

    def __init__(self, locs=[]):
        super(AnnotatedCFGPath, self).__init__([AnnotatedCFGPath.AnnotatedLoc(l) for l in locs])
        self.locannotations = {}
        self.locannotationsafter = {}

    def addLocAnnotationAfter(self, annot, loc):
        if isinstance(loc, AnnotatedCFGPath.AnnotatedLoc):
            loc = loc.loc
        assert isinstance(loc, CFG.AnnotatedNode), loc
        self.locannotationsafter.setdefault(loc, []).append(annot)

    def getLocAnnotationsAfter(self, loc):
        if isinstance(loc, AnnotatedCFGPath.AnnotatedLoc):
            loc = loc.loc
        assert isinstance(loc, CFG.AnnotatedNode), loc
        return self.locannotationsafter.get(loc)

    def addLocAnnotationBefore(self, annot, loc):
        if isinstance(loc, AnnotatedCFGPath.AnnotatedLoc):
            loc = loc.loc
        assert isinstance(loc, CFG.AnnotatedNode), loc
        self.locannotations.setdefault(loc, []).append(annot)

    def getLocAnnotationsBefore(self, loc):
        if isinstance(loc, AnnotatedCFGPath.AnnotatedLoc):
            loc = loc.loc
        assert isinstance(loc, CFG.AnnotatedNode), loc
        return self.locannotations.get(loc)


    def addAnnotationAfter(self, annot, idx=0):
        """
        Add annotation to the given location on the path.
        The annotation should be evaluated "after"
        executing the location.
        """
        assert idx < self.length()
        self.locations[idx].annotationsAfter.append(annot)

    def addAnnotationBefore(self, annot, idx=0):
        """
        Add annotation to the given location on the path.
        The annotation should be evaluated "before"
        executing the location.
        """
        assert idx < self.length()
        self.locations[idx].annotationsBefore.append(annot)

    def copyandprepend(self, loc):
        n = deepcopy(self)
        # FIXME: this is not efficient...
        n.locations = [AnnotatedCFGPath.AnnotatedLoc(loc)] + n.locations

        return n


