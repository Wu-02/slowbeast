from slowbeast.analysis.dfs import DFSVisitor
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath

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

class SimpleLoop:
    """
    Represents a set of paths loc --> loc
    such that all these paths are acyclic
    """
    def __init__(self, loc, paths, exits):
        self.loc = loc
        self.paths = paths
        self.exits = exits

    def getPaths(self):
        return self.paths

    def getExits(self):
        return self.exits

    def construct(loc):
        """
        Construct the SimpleLoop obj for loc.
        Returns None if that cannot be done
        """
        workbag = [[loc]]
        paths = []
        exits = set()
        while workbag:
            newworkbag = []
            for p in workbag:
                succs = p[-1].getSuccessors()
                if len(succs) == 0:
                    exits.add((p[1]))
                else:
                    for s in succs:
                        if s == loc:
                            p.append(s)
                            paths.append(AnnotatedCFGPath(p))
                        elif s in p: #FIXME: not very efficient
                            if reachable(p[-1], loc):
                                return None # cyclic path
                            else:
                                exits.add((p[1]))
                        else:
                            newworkbag.append(p + [s])
            workbag = newworkbag
        
        return SimpleLoop(loc, paths, [AnnotatedCFGPath([loc, e]) for e in exits])
