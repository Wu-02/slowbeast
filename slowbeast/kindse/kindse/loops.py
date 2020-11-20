from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.symexe.annotations import InstrsAnnotation
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath
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
        self._exits = exits         # edges leaving the loop
        self._entries = entries     # edges from outside to loop header
        self._inedges = inedges     # edges from header into loop
        self._backedges = backedges # edges from loop into header

        # the state after executing the given path
        self.states = None
        self.vars = None

    def header(self):
        return self._header

    def locs(self):
        return self._locs

    def has_loc(self, l):
        return l in self._locs

    def __contains__(self, item):
        return item in self._locs

    def getPaths(self):
        return self._paths

    def getExits(self):
        return self._exits

    def getEntries(self):
        return self._entries

    def get_inedges(self):
        return self._inedges

    def construct(loc):
        """
        Construct the SimpleLoop obj for _header.
        Returns None if that cannot be done
        """

        backedges = set()
        locs = set()
        locs.add(loc)

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                if end == loc:
                    backedges.add((start, end))
                else:
                    raise ValueError("Nested loop")
            if dfstype != DFSEdgeType.TREE and end in locs:
                # backtrack is not called for non-tree edges...
                locs.add(start)

        def backtrack(start, end):
            if start is not None and end in locs:
                locs.add(start)

        try:
            DFSVisitor().foreachedge(loc, processedge, backtrack)
        except ValueError: # nested loop
            return None

        entries = set()
        inedges = set()
        exits = set()
        # FIXME: do not store this, just return generators from getters (except for exits, thos need to be precomputed)
        for succ in loc.getSuccessors():
            if succ in locs:
                inedges.add((loc, succ))
            else:
                exits.add((loc, succ))
        for pred in loc.getPredecessors():
            if pred not in locs:
                entries.add((pred, loc))

        # fixme: not efficient at all...
        paths = []
        queue = [[l, e] for l, e in inedges]
        while queue:
            newqueue = []
            for path in queue:
                for succ in path[-1].getSuccessors():
                    if succ not in locs:
                        exits.add((path[-1], succ))
                        continue
                    np = path + [succ]
                    if succ != loc:
                        newqueue.append(np)
                    else:
                        paths.append(np)
            queue = newqueue

        return SimpleLoop(loc,
                          [AnnotatedCFGPath(p) for p in paths],
                          locs, entries, exits, inedges, backedges)


    def getVariables(self):
        V = set()
        for p in self._paths:
            for loc in p:
                for L in (
                    l for l in loc.getBBlock().instructions() if isinstance(l, Load)
                ):
                    op = L.getPointerOperand()
                    if isinstance(op, Alloc):
                        V.add(op)
        self.vars = {v: None for v in V}

    def computeMonotonicVars(self, executor):
        """
        Compute how the value of loads changes in this loop.
        NOTE: this is not the same as how the value of "variables"
        changes. E.g., if there is a load that can be executed only
        once on the path, it must necessarily have invariant value,
        although the memory from which it load may change.
        """

        dbg_sec(
            f"Checking monotonicity of variables in simple loop"
            f" over {self._header.getBBlock().get_id()}"
        )
        if self.vars is None:
            self.getVariables()

        results = {}

        def addRel(x, r):
            assert r in [None, "<", "<=", ">", ">=", "="]
            # group by the allocations
            x = x.load.getPointerOperand()
            n = results.setdefault(x, "?")
            # print(x, n, r)
            if n is None:
                return

            if r is None:
                results[x] = None
            if n == "?":  # first assignment
                results[x] = r
            elif n != r:
                if n == "<" and r == "<=":
                    results[x] = "<="
                elif n == "<=" and r in ["<", "="]:
                    pass
                elif n == ">" and r == ">=":
                    results[x] = ">="
                elif n == ">=" and r in [">", "="]:
                    pass
                elif n == "=" and r in [">=", "<="]:
                    results[x] = r
                else:
                    assert (n == "=" and r in [">", "<"]) or (
                        r == "=" and n in [">", "<"]
                    )
                    results[x] = None
            else:
                assert n == r and n is not None and n != "?"

        V = self.vars.keys()
        loads = [Load(v, v.getSize().value()) for v in V]
        for p in self._paths:
            path = p.copy()
            path.addLocAnnotationBefore(InstrsAnnotation(loads), self._header)
            r = executor.executePath(path)
            assert r.errors is None
            assert r.other is None

            ready = r.ready
            if not ready:
                continue

            for s in ready:
                # NOTE: we do not need to handle the cases when x is not
                # present in the state, because in that case
                # it is invariant for the path
                for x in (
                    l for l in s.getNondets() if l.isNondetLoad() and l.load in loads
                ):
                    curval = s.get(x.load)
                    assert curval, "BUG: must have the load as it is nondet"
                    addRel(x, get_rel(s, x, curval))

        V = self.vars
        for (x, r) in results.items():
            # print(x, r)
            V[x] = r
