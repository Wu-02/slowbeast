from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.symexe.annotations import InstrsAnnotation
from slowbeast.analysis.cfa import CFA
from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.util.debugging import dbg_sec
from slowbeast.ir.instruction import Load, Alloc


def reachable(node, what):
    def _reachable(node, what, visited):
        if node == what:
            return True

        visited[node] = True
        for s in node.getSuccessors():
            if visited.setdefault(s, False):
                continue
            if _reachable(s, what, visited):
                return True

        return False

    visited = {}
    return _reachable(node, what, visited)


def get_rel(s, x, curval):
    EM = s.getExprManager()
    Lt = EM.Lt
    Gt = EM.Gt
    Eq = EM.Eq

    lt = s.is_sat(Lt(x, curval))
    gt = s.is_sat(Gt(x, curval))

    if lt is False:  # x >= cur
        if gt is False:  # x <= cur
            assert s.is_sat(EM.Ne(x, curval)) is False
            return "="
        elif gt is True:  # x >= cur
            if s.is_sat(Eq(x, curval)) is False:
                return ">"
            else:
                return ">="
    elif lt is True:
        if gt is False:  # x <= cur
            if s.is_sat(Eq(x, curval)) is False:
                return "<"
            return "<="

    return None


class SimpleLoop:
    """
    Represents a set of _paths _header --> _header
    such that all these _paths are acyclic
    """

    def __init__(self, loc, paths, locs, entries, exits, inedges, backedges):
        self._header = loc
        # header-header _paths
        self._paths = paths
        # _paths inside the loop that do not return to the header
        # the last edge from each path is also an exit (but one that does
        # not go through the loop header)
        self._locs = locs
        self._exits = exits  # edges leaving the loop
        self._entries = entries  # edges from outside to loop header
        self._inedges = inedges  # edges from header into loop
        self._backedges = backedges  # edges from loop into header
        self._edges = set(e for path in paths for e in path)

        # the state after executing the given path
        self.states = None
        self.vars = None

    def header(self):
        return self._header

    def locs(self):
        return self._locs

    def has_loc(self, l):
        return l in self._locs

    def __contains__(self, item: CFA.Edge):
        assert isinstance(item, CFA.Edge)
        return item in self._edges

    def getPaths(self):
        return self._paths

    def get_exit_paths(self):
        """
        Take all paths in the loop and prolong them such that they end with an exit edge.
        """
        result = []
        queue = self._paths.copy()
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    if succedge in self._exits:
                        result.append(path.copyandappend(succedge))
                    elif succedge not in self._backedges:
                        newqueue.append(path.copyandappend(succedge))
                    # else drop the path
            queue = newqueue
        return result

    def getExits(self):
        return self._exits

    def getEntries(self):
        return self._entries

    def get_inedges(self):
        return self._inedges

    def has_inedge(self, *args):
        if len(args) == 1:
            assert isinstance(args[0], CFA.Edge)
            s, t = args[0].source(), args[0].target()
        elif len(args) == 2:
            s, t = args[0], args[1]
        else:
            raise RuntimeError("Invalid arguments to has_inedge")

        assert isinstance(s, CFA.Location)
        assert isinstance(t, CFA.Location)
        for edge in self._inedges:
            if edge.source() == s and edge.target() == t:
                return True
        return False

    def construct(loc):
        """
        Construct the SimpleLoop obj for _header.
        Returns None if that cannot be done
        """

        backedges = set()
        locs = set()
        locs.add(loc)

        def processedge(edge, dfstype):
            start, end = edge.source(), edge.target()
            if dfstype == DFSEdgeType.BACK:
                if end == loc:
                    backedges.add(edge)
                else:
                    raise ValueError("Nested loop")
            if dfstype != DFSEdgeType.TREE and end in locs:
                # backtrack is not called for non-tree edges...
                locs.add(start)

        def backtrack(edge):
            if edge is not None and edge.target() in locs:
                locs.add(edge.source())

        try:
            DFSVisitor().foreachedge(loc, processedge, backtrack)
        except ValueError:  # nested loop
            return None

        entries = set()
        inedges = set()
        exits = set()
        # FIXME: do not store this, just return generators from getters (except for exits, those need to be precomputed)
        for edge in loc.successors():
            if edge.target() in locs:
                inedges.add(edge)
            else:
                exits.add(edge)
        for edge in loc.predecessors():
            if edge.source() not in locs:
                entries.add(edge)

        # fixme: not efficient at all...
        paths = []
        queue = [[e] for e in inedges]
        while queue:
            newqueue = []
            for path in queue:
                for succedge in path[-1].successors():
                    succloc = succedge.target()
                    if succloc not in locs:
                        exits.add(succedge)
                        continue
                    np = path + [succedge]
                    if succloc != loc:
                        newqueue.append(np)
                    else:
                        paths.append(np)
            queue = newqueue

        return SimpleLoop(
            loc,
            [AnnotatedCFAPath(p) for p in paths],
            locs,
            entries,
            exits,
            inedges,
            backedges,
        )
