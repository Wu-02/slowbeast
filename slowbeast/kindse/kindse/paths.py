from slowbeast.analysis.dfs import DFSVisitor
from slowbeast.symexe.pathexecutor import InstrsAnnotation
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

    if lt is False: # x >= cur
        if gt is False: # x <= cur
            assert s.is_sat(EM.Ne(x, curval)) is False
            return '='
        elif gt is True: # x >= cur
            if s.is_sat(Eq(x, curval)) is False:
                return '>'
            else:
                return '>='
    elif lt is True:
        if gt is False: # x <= cur
            if s.is_sat(Eq(x, curval)) is False:
                return '<'
            return '<='

    return None

class SimpleLoop:
    """
    Represents a set of paths loc --> loc
    such that all these paths are acyclic
    """
    def __init__(self, loc, paths, exits):
        self.loc = loc
        self.paths = paths
        self.exits = exits

        self.vars = None

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

    def getVariables(self):
        V = set()
        for p in self.paths:
            for loc in p:
                for L in (l for l in loc.getBBlock().getInstructions() if isinstance(l, Load)):
                    op = L.getPointerOperand()
                    if isinstance(op, Alloc):
                        V.add(op)
        self.vars = {v : None for v in V}

    def computeMonotonicVars(self, executor):
        """
        Compute how the value of loads changes in this loop.
        NOTE: this is not the same as how the value of "variables"
        changes. E.g., if there is a load that can be executed only
        once on the path, it must necessarily have invariant value,
        although the memory from which it load may change.
        """

        dbg_sec(f"Checking monotonicity of variables in simple loop"\
                f" over {self.loc.getBBlock().getID()}")
        if self.vars is None:
            self.getVariables()

        results = {}

        def addRel(x, r):
            assert r in [None, '<', '<=', '>', '>=', '=']
            # group by the allocations
            x = x.load.getPointerOperand()
            n = results.setdefault(x, '?')
            #print(x, n, r)
            if n is None:
                return


            if r is None:
                results[x] = None
            if n == '?': # first assignment
               results[x] = r
            elif n != r:
                if n == '<' and r == '<=':
                    results[x] = '<='
                elif n == '<=' and r in ['<', '=']:
                    pass
                elif n == '>' and r == '>=':
                    results[x] = '>='
                elif n == '>=' and r in ['>', '=']:
                    pass
                elif n == '=' and r in ['>=', '<=']:
                    results[x] = r
                else:
                    assert (n == '=' and r in ['>', '<']) or\
                           (r == '=' and n in ['>', '<'])
                    results[x] = None
            else:
                assert n == r and n is not None and n != '?'
            
        V = self.vars.keys()
        loads = [Load(v, v.getSize().getValue()) for v in V]
        for p in self.paths:
            path = p.copy()
            path.addLocAnnotationBefore(InstrsAnnotation(loads), self.loc)
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
                for x in (l for l in s.getNondets() if l.isNondetLoad()):
                    assert x.load in loads, "BUG: have also other loads than our artificial"
                    curval = s.get(x.load)
                    assert curval, "BUG: must have the load as it is nondet"
                    addRel(x, get_rel(s, x, curval))

        V = self.vars
        for (x, r) in results.items():
            #print(x, r)
            V[x] = r

