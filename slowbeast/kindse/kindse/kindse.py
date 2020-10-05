from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.pathexecutor import InstrsAnnotation, AssumeAnnotation, AssertAnnotation
from slowbeast.domains.symbolic import NondetLoad
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from . paths import SimpleLoop
from . annotations import InvariantGenerator, execute_loop, exec_on_loop, get_inv_candidates
from . kindsebase import KindSymbolicExecutor as BaseKindSE

def state_to_annotation(state):
    EM = state.getExprManager()
    return AssumeAnnotation(state.getConstraintsObj().asFormula(EM),
                            {l : l.load for l in state.getNondetLoads()},
                            EM)

def unify_annotations(annot1, annot2, EM):
    """ Take two annotations, unify their variables and "or" them together """

    subs1 = annot1.getSubstitutions()
    subs2 = annot2.getSubstitutions()
    expr1 = annot1.getExpr()
    expr2 = annot2.getExpr()
    if 0 < len(subs2) < len(subs1) or len(subs1) == 0:
        subs1, subs2 = subs2, subs1
        expr1, expr2 = expr2, expr1

    if len(subs1) == 0:
        assert len(subs2) == 0
        return AssumeAnnotation(EM.simplify(EM.Or(expr1, expr2)), {}, EM)

    subs = {}
    col = False
    for (val, instr) in subs1.items():
        instr2 = subs2.get(val)
        if instr2 and instr2 != instr:
            # collision
            freshval = EM.freshValue(val.name(), bw=val.getType().getBitWidth())
            ndload = NondetLoad.fromExpr(freshval, val.load, val.alloc)
            expr2 = EM.substitute(expr2, (val, ndload))
            subs[ndload] = instr2

        # always add this one
        subs[val] = instr

    # add the rest of subs2
    for (val, instr) in subs2.items():
        if not subs.get(val):
            subs[val] = instr

    return AssumeAnnotation(EM.simplify(EM.Or(expr1, expr2)), subs, EM)

def states_to_annotation(states):
    a = None
    for s in states:
        EM = s.getExprManager()
        a = unify_annotations(a or AssumeAnnotation(EM.getFalse(), {}, EM),
                              state_to_annotation(s), EM)
    return a
 
def abstract(r, post):
    for inv in get_inv_candidates(r):
        return inv
    return None
    
def strengthen(executor, prestates, A, Sind, loc, L):
    T = unify_annotations(A, Sind, getGlobalExprManager())
    r = exec_on_loop(loc, executor, L, pre=[A], post=[T])
    while r.errors:
        break

    if not r.errors:
        return A
    # we failed...
    return None

class KindSymbolicExecutor(BaseKindSE):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions(),
            genannot=True):
        super(
            KindSymbolicExecutor,
            self).__init__(
            prog=prog,
            testgen=testgen,
            opts=opts)

        self.readypaths = []
        self.stalepaths = []

        self.genannot = genannot
        self.invpoints = {}
        self.have_problematic_path = False
        self.loops = {}

    def handle_loop(self, loc, states):
        self.loops.setdefault(loc.getBBlockID(), []).append(states)

       #if any(map(lambda p: self.is_inv_loc(p.first()), self.stalepaths)) or\
       #   any(map(lambda p: self.is_inv_loc(p.first()), self.readypaths)):
       #   return

        assert self.loops.get(loc.getBBlockID())
        self.execute_loop(loc, self.loops.get(loc.getBBlockID()))

    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            raise NotImplementedError("We must execute the loop normally")
            return None

        # NOTE: Safe states are the complement of error states,
        # but are not inductive on the loop header -- what we need is to
        # have safe states that already left the loop (i.e., complement of
        # error states intersected with the negation of loop condition).
        # Ready and terminated states on the paths from header to the error
        # could be used, but are not all the safe states (there may be safe
        # states that miss the assertion)

        S = None # safe states
        H = None # negation of loop condition
        for u in unsafe:
            EM = u.getExprManager()
            S = unify_annotations(S or AssumeAnnotation(EM.getFalse(), {}, EM),
                                  state_to_annotation(u), EM)
            H = EM.Or(H or EM.getFalse(), u.getConstraints()[0])

        # FIXME: EM is out of scope
        # This is the first inductive set on H
        S = AssumeAnnotation(EM.simplify(EM.And(EM.Not(S.getExpr()), H)),
                             S.getSubstitutions(), EM)
        Serr = AssertAnnotation(S.getExpr(), S.getSubstitutions(), EM)
        #print('F0', S)
        if __debug__:
            r = exec_on_loop(loc, self, L, pre=[S], post=[Serr])
            assert r.errors is None


        # FIXME: EM is out of scope
        print('--- starting executing ---')
        EM = getGlobalExprManager()
        while True:
            print('--- iter ---')
            r = exec_on_loop(loc, self, L, post=[Serr])

            # NOTE: we must use Not(r.errors), r.ready does not yield inductive set
            # for some reason... why? Why, oh, why? One would think they are
            # complements... 
            A = abstract(r, Serr)
            if A is None:
                A = states_to_annotation(r.errors).Not(EM)
            S = strengthen(self, r, A, Serr, loc, L)
            if S is None:
                S = states_to_annotation(r.errors).Not(EM)

            S = unify_annotations(S, Serr, EM)
            if S == Serr: # we got syntactically the same formula
                print('breaking', S)
                Serr = AssertAnnotation(S.getExpr(), S.getSubstitutions(), EM)
                newpaths = []
                for p in L.getEntries():
                    a = AnnotatedCFGPath([p, loc])
                    a.addPostcondition(Serr)
                    print(a)
                    newpaths.append(a)
                self.queue_paths(newpaths)
                break

            Serr = AssertAnnotation(S.getExpr(), S.getSubstitutions(), EM)
            if __debug__:
                # debugging check -- S should be now inductive on loc
                r = exec_on_loop(loc, self, L, pre=[S], post=[Serr])
                assert r.errors is None, "S is not inductive"
                print(f"{S} is inductive...")


    def check_path(self, path):
        first_loc = path.first()
        if self._is_init(first_loc):
            r, states = self.checkInitialPath(path)
            if r is Result.UNSAFE:
                self.reportfn(f"Error path: {path}", color="RED")
                return r, states  # found a real error
            elif r is Result.SAFE:
                self.reportfn(f"Safe (init) path: {path}", color="DARK_GREEN")
                return None, states  # this path is safe
            elif r is Result.UNKNOWN:
                self.have_problematic_path = True
                # there is a problem with this path,
                # but we can still find an error
                # on some different path
                # FIXME: keep it in queue so that
                # we can rule out this path by
                # annotations from other paths?
                return None, states
            assert r is None, r

        r = self.executePath(path)

        killed = (s for s in r.other if s.wasKilled()) if r.other else None
        if killed:
            self.have_problematic_path = True
            for s in killed:
                self.report(s)

        if r.errors:
            self.reportfn(f"Possibly error path: {path}", color="ORANGE")
        else:
            self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        return None, r

    def findInvPoints(self, cfg):
        points = []

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                points.append(end)

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        paths = []
        for F in self.getProgram().getFunctions():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            invpoints = self.findInvPoints(cfg)
            self.invpoints[cfg] = invpoints

            nodes = cfg.getNodes()
            npaths = [AnnotatedCFGPath([n]) for n in nodes if n.hasAssert()]
            step = self.getOptions().step
            while k > 0:
                npaths = [
                    np for p in npaths for np in self.extendPath(
                        p, steps=step, atmost=True,
                        stoppoints=invpoints)]
                k -= 1
            paths += npaths

        return paths

    def get_path_to_run(self):
        ready = self.readypaths
        if not ready:
            ready = self.stalepaths
        if ready:
            return ready.pop()
        return None

    def is_inv_loc(self, loc):
        assert isinstance(loc, CFG.AnnotatedNode), loc
        return loc in self.invpoints[loc.getCFG()]

    def queue_paths(self, paths):
        is_inv_loc = self.is_inv_loc
        for p in paths:
            if is_inv_loc(p.first()):
                self.stalepaths.append(p)
            else:
                self.readypaths.append(p)

    def extend_and_queue_paths(self, path):
        step = self.getOptions().step
        newpaths = self.extendPath(path,
                                   steps=step,
                                   atmost=step != 1,
                                   stoppoints=self.invpoints[path[0].getCFG()])
        self.queue_paths(newpaths)
       
    def run(self, paths=None, maxk=None):
        k = 1

        if paths is None:
            paths = self.initializePaths()
        self.queue_paths(paths)

        while True:
            dbg(f"Got {len(self.readypaths)} paths ready and {len(self.stalepaths)} waiting")

            path = self.get_path_to_run()
            if path is None:
                if self.have_problematic_path:
                    print_stdout("Enumerating paths finished, but a problem was met.", color='ORANGE')
                    return 1

                print_stdout("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color='RED')
                return 1
            elif states.errors: # got error states that may not be real
                assert r is None
                if self.is_inv_loc(path.first()):
                    self.handle_loop(path.first(), states)
                else:
                    self.extend_and_queue_paths(path)

            k += 1
            if maxk and maxk <= k:
                print_stdout(
                    "Hit the maximal number of iterations, giving up.",
                    color='ORANGE')
                return 1
