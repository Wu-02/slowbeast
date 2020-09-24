from .. analysis.cfg import CFG as PureCFG
from .. analysis.cfg import CFGPath as PureCFGPath
from .. ir.instruction import Assert
from .. ir.bblock import BBlock

from copy import deepcopy


class CFG(PureCFG):
    """
    CFG with nodes annotated with information
    about possible error sites and other
    useful information.
    """

    class AnnotatedNode(PureCFG.Node):
        __slots__ = ['_has_assert', 'annotationsAfter', 'annotationsBefore']

        def __init__(self, cfg, B):
            super(CFG.AnnotatedNode, self).__init__(cfg, B)
            # find out whether this node has an assert
            self._has_assert = False
            for i in B.getInstructions():
                if isinstance(i, Assert):
                    self._has_assert = True
                    break

            # after loc execution
            self.annotationsAfter = []
            # before loc execution
            self.annotationsBefore = []

        def hasAssert(self):
            return self._has_assert

        def addAnnotationAfter(self, annot):
            """
            The annotation should be evaluated "after"
            executing the location.
            """
            self.annotationsAfter.append(annot)

        def addAnnotationBefore(self, annot):
            """
            The annotation should be evaluated "before"
            executing the location.
            """
            self.annotationsBefore(annot)

    def __init__(self, F):
        super(CFG, self).__init__(F)

    def createNode(self, *args):
        assert len(args) == 1
        return CFG.AnnotatedNode(self, *args)


class CFGPath(PureCFGPath):
    def __init__(self, locs=[]):
        super(CFGPath, self).__init__(locs)

    def reachesAssert(self):
        if len(self.locations) <= 0:
            return False

        return self.locations[-1].hasAssert()


def _get_loc_key(loc):
    if isinstance(loc, CFG.AnnotatedNode):
        return loc.getBBlock().getID()
    elif isinstance(loc, BBlock):
        return loc.getID()
    else:
        raise NotImplementedError(f"Unhandled key value: {loc}")


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
        self.locannotations = {}
        self.locannotationsafter = {}

    def addLocAnnotationAfter(self, annot, loc):
        self.locannotationsafter.setdefault(
            _get_loc_key(loc), []).append(annot)

    def getLocAnnotationsAfter(self, loc):
        return self.locannotationsafter.get(_get_loc_key(loc))

    def addLocAnnotationBefore(self, annot, loc):
        self.locannotations.setdefault(_get_loc_key(loc), []).append(annot)

    def getLocAnnotationsBefore(self, loc):
        return self.locannotations.get(_get_loc_key(loc))

    # def addAnnotationAfter(self, annot, idx=0):
    #    """
    #    Add annotation to the given location on the path.
    #    The annotation should be evaluated "after"
    #    executing the location.
    #    """
    #    assert idx < self.length()
    #    self.locations[idx].annotationsAfter.append(annot)

    # def addAnnotationBefore(self, annot, idx=0):
    #    """
    #    Add annotation to the given location on the path.
    #    The annotation should be evaluated "before"
    #    executing the location.
    #    """
    #    assert idx < self.length()
    #    self.locations[idx].annotationsBefore.append(annot)

    def copyandprepend(self, loc):
        # do deep copy to copy also the annotations
        n = deepcopy(self)
        # FIXME: this is not efficient...
        n.locations = [loc] + n.locations

        return n
