from slowbeast.analysis.cfa import CFA
from slowbeast.ir.instruction import Assert

def _loc_id(loc):
    if isinstance(loc, int):
        return loc
    return loc.id()

def _edge_str(edge, ab, aa):
    return "({0}{1}{2} -> {3}{4}{5})".format(
        "@ " if ab.get(_loc_id(edge.source())) else "",
        edge.source(),
        " @" if aa.get(_loc_id(edge.source())) else "",
        "@ " if ab.get(_loc_id(edge.target())) else "",
        edge.target(),
        " @" if aa.get(_loc_id(edge.source())) else "")

def _copy_annots(dst, src):
    # FIXME: do cow?
    dst._annot_after_loc = src._annot_after_loc.copy()
    dst._annot_before_loc = src._annot_before_loc.copy()
    dst._annot_before = src._annot_before.copy()
    dst._annot_after = src._annot_after.copy()


class AnnotatedCFAPath:
    """
    A CFA path that contains annotations. These annotations can put assumptions
    on values or similar. The annotations are a special set of instructions that
    are executed on given places.
    """

    __slots__ = "_edges", "_annot_after_loc", "_annot_before_loc", "_annot_before", "_annot_after"

    def __init__(self, edges=[]):
        self._edges = edges
        self._annot_after_loc = {}
        self._annot_before_loc = {}
        self._annot_before = []
        self._annot_after = []

    def get_first_inst(self):
        edges = self._edges
        if edges:
            for e in edges:
                elems = e.elems()
                if elems: # edge may be empty
                    return elems[0]
        return None

    def edges(self):
        return self._edges

    def __getitem__(self, item):
        return self._edges.__getitem__(item)

    def annot_after_loc(self, loc):
        return self._annot_after_loc.get(_loc_id(loc))

    def annot_before_loc(self, loc):
        return self._annot_before_loc.get(_loc_id(loc))

    def annot_before(self):
        return self._annot_before

    def annot_after(self):
        return self._annot_after

    def add_annot_after(self, annot):
        self._annot_after.append(annot)

    def add_annot_before(self, annot):
        self._annot_before.append(annot)

    def add_annot_after_loc(self, annot, loc):
        self._annot_after_loc.setdefault(_loc_id(loc), []).append(annot)

    def add_annot_before_loc(self, annot, loc):
        self._annot_before_loc.setdefault(_loc_id(loc), []).append(annot)

    def subpath(self, start, end):
        n = AnnotatedCFAPath(self._edges[start:end+1])
        _copy_annots(n, self)
        return n

    def copy(self):
        n = AnnotatedCFAPath(self._edges.copy())
        _copy_annots(n, self)
        return n

    def copyandprepend(self, edge):
        # FIXME: this is not efficient...
        n = AnnotatedCFAPath([edge] + self._edges)
        _copy_annots(n, self)
        return n

    def copyandappend(self, edge):
        # FIXME: this is not efficient...
        n = AnnotatedCFAPath(self._edges + [edge])
        _copy_annots(n, self)
        return n

    def copyandsetpath(self, locs):
        n = AnnotatedCFAPath(locs)
        _copy_annots(n, self)
        return n

    def __len__(self):
        return len(self._edges)

    def __repr__(self):
        ab, aa = self._annot_before_loc, self._annot_after_loc
        return "{0}{1}{2}".format(
            "A " if self._annot_before else "",
            "".join(map(lambda e: _edge_str(e, ab, aa), self.edges())),
            " A" if self._annot_after else "",
        )

