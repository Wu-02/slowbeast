from slowbeast.util.debugging import print_stdout, dbg, dbg_sec

from slowbeast.core.executor import PathExecutionResult
from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import (
    KindSymbolicExecutor as BasicKindSymbolicExecutor,
)
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.symexe.annotations import (
    AssumeAnnotation,
    AssertAnnotation,
    state_to_annotation,
    states_to_annotation,
    or_annotations,
    and_annotations,
    unify_annotations,
)

from slowbeast.symexe.statesset import union, intersection, complement
from slowbeast.solvers.solver import getGlobalExprManager, Solver

from .loops import SimpleLoop
from .relations import get_safe_relations, get_safe_subexpressions
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence


def overapproximations(s, unsafe):
    yield from get_safe_relations([s], unsafe)
    yield from get_safe_subexpressions(s, unsafe)


def abstract(executor, state, unsafe):
    """
    unsafe - unsafe states from the last step
    """
    yield from overapproximations(state, unsafe)


def _simplify_with_assumption(lhs, rhs):
    """
    Remove from 'rhs' (some) parts implied by the 'lhs'
    'rhs' is a list of Or expressions
    'lhs' is a list of Or expressions
    """
    # FIXME do this with an incremental solver
    assumptions = lhs.copy()

    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in rhs:
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)

    assumptions += singletons

    # remove the implied parts of the rest of clauses
    changed = False
    newrhs = []
    newsingletons = []
    solver = Solver()
    EM = getGlobalExprManager()
    Not = EM.Not
    for c in rest:
        newliterals = []
        for l in c.children():
            assert l.isBool()
            q = solver.is_sat(*assumptions, l)
            if q is not False:
                q = solver.is_sat(*assumptions, Not(l))
                if q is False:
                    # this literal is implied and thus the whole clause is true
                    changed = True
                    break
                else:
                    # we know that the literal can be true
                    # or the solver failed, so keep the literal
                    newliterals.append(l)
            else:
                # we dropped the literal
                changed = True

        assert len(newliterals) > 0, "Unsat clause..."
        if len(newliterals) == 1:
            # XXX: we could do this also for non-singletons,
            # but do we want to?
            assumptions.append(literals[0])
            newsingletons.append(literals[0])
        else:
            newrhs.append(newliterals)

    # get rid of redundant singletons
    assumptions = lhs.copy()
    tmp = []
    for c in singletons:
        assert c.isBool()
        q = solver.is_sat(*assumptions, Not(c))
        if q is False:
            # this literal is implied and we can drop it
            changed = True
            continue
        else:
            # we know that the literal can be true
            # or the solver failed, so keep the literal
            tmp.append(c)
    singletons = tmp

    return newsingletons, singletons + newrhs, changed


def simplify_with_assumption(lhs, rhs):
    lhs = list(lhs.to_cnf().children())
    rhs = list(rhs.to_cnf().children())
    changed = True

    while changed:
        singletons, rhs, changed = _simplify_with_assumption(lhs, rhs)
        lhs += singletons

    return getGlobalExprManager().conjunction(*rhs)

def remove_implied_literals(clauses, unsafe):
    # split clauses to singleton clauses and the others
    singletons = []
    rest = []
    for c in clauses:
        if c.isOr():
            rest.append(c)
        else:  # the formula is in CNF, so this must be a singleton
            singletons.append(c)

    assumptions = []

    solver = Solver()
    Not = getGlobalExprManager().Not
    i = 0
    while True:
        if i >= len(singletons):
            break
        tmp = [singletons[i]]
        for j in range(0, len(singletons)):
            if i == j:
                continue
            c = singletons[j]
            assert c.isBool()
            q = solver.is_sat(*tmp, Not(c))
            if q is False:
                # this literal is implied and we can drop it,
                # but only if  it does not render the formula unsafe
                assert intersection(unsafe, tmp).is_empty(), f"{unsafe} \cap {tmp}"
            else:
                # we know that the literal can be true
                # or the solver failed, so keep the literal
                tmp.append(c)
        singletons = tmp
        i += 1

    return singletons + rest


def strengthenSafe(executor, s, a, seq, errs0, L):
    # if the annotations intersect, remove errs0 from a
    EM = getGlobalExprManager()

    # FIXME: proceed only when a intersects errs0

    # NOTE: the strengthening is the loop-exit condition.
    # It is sufficient to exclude the unsafe states
    states, stren, subs, noterrstates = None, None, None, None
    if errs0.strengthening:
        if a.strengthening is None:
            noterrstates = errs0.strengthening.Not(EM)
        else:
            noterrstates = and_annotations(
                EM, True, a.strengthening, errs0.strengthening.Not(EM)
            )
    else:
        # the error loc is inside a loop - we must use the whole error
        # states decription
        # FIXME: try use only a part of the condition (unsat core)
        assert errs0.states
        if a.strengthening is None:
            noterrstates = errs0.states.Not(EM)
        else:
            noterrstates = and_annotations(
                EM, True, a.strengthening, errs0.states.Not(EM)
            )
    states, stren, subs = unify_annotations(EM, a.states, noterrstates)
    A1 = AssertAnnotation(states, subs, EM)
    A2 = AssertAnnotation(stren, subs, EM)
    return InductiveSequence.Frame(A1, A2)


def check_inv(prog, L, inv):
    loc = L.loc
    dbg_sec(f"Checking if {inv} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    newpaths = []
    for p in L.getEntries():
        apath = AnnotatedCFGPath([p, loc])
        apath.addLocAnnotationBefore(inv, loc)
        newpaths.append(apath)

    maxk = 5
    dbg_sec("Running nested KindSE")
    res = kindse.run(newpaths, maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0


def get_initial_seq(unsafe):
    """
    Return two annotations, one that is the initial safe sequence
    and one that represents the error states
    """
    # NOTE: Only safe states that reach the assert are not inductive on the
    # loop header -- what we need is to have safe states that already left
    # the loop and safely pass assertion or avoid it.
    # These are the complement of error states intersected with the
    # negation of loop condition.

    S = None  # safe states
    E = None  # safe states
    H = None  # loop exit condition

    EM = getGlobalExprManager()
    Not = EM.Not
    for u in unsafe:
        # add constraints without loop exit condition
        # (we'll add the loop condition later)
        uconstr = u.getConstraints()
        # same as uconstr[1:], but via generators
        uconstrnh = (c for (n, c) in enumerate(uconstr) if n > 0)
        # safe states
        notu = EM.disjunction(*map(Not, uconstrnh))
        S = EM.And(notu, S) if S else notu  # use conjunction too?
        # unsafe states
        su = EM.conjunction(*(c for (n, c) in enumerate(uconstr) if n > 0))
        E = EM.Or(su, E) if E else su

        # loop exit condition
        H = EM.Or(H, uconstr[0]) if H else uconstr[0]

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sh = AssertAnnotation(H, subs, EM)
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, Sh), InductiveSequence.Frame(Se, Sh)


def check_paths(executor, paths, pre=None, post=None):
    #print_stdout(f'Check paths with PRE={pre} and POST={post}', color="BLUE")
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.addPostcondition(post.as_assert_annotation())

        if pre:
            p.addPrecondition(pre.as_assume_annotation())

        r = executor.executePath(p)
        result.merge(r)

    #print_stdout(str(result), color="ORANGE")
    return result


def literals(c):
    if c.isOr():
        yield from c.children()
    yield c


def get_predicate(l):
    EM = getGlobalExprManager()
    if l.isLe():
        return EM.Le
    if l.isGe():
        return EM.Ge
    if l.isLt():
        return EM.Lt
    if l.isGt():
        return EM.Gt

    raise NotImplementedError(f"Unhandled predicate in expr {l}")


def decompose_literal(l):
    isnot = False
    if l.isNot():
        isnot = True
        l = list(l.children())[0]

    if l.isLt() or l.isLe():
        addtoleft = False
    elif l.isGt() or l.isGe():
        addtoleft = True
    else:
        return None, None, None, None

    chld = list(l.children())
    assert len(chld) == 2
    left, P, right = chld[0], get_predicate(l), chld[1]

    if isnot:
        addtoleft = not addtoleft
        EM = getGlobalExprManager()
        binop = P
        P = lambda a, b: EM.Not(binop(a, b))

    return left, right, P, addtoleft

def get_left_right(l):
    if l.isNot():
        l = list(l.children())[0]

    chld = list(l.children())
    assert len(chld) == 2, "Invalid literal (we assume binop or not(binop)"
    return chld[0], chld[1]

def overapprox_literal(l, S, unsafe, target, executor, L):
    assert intersection(S, l, unsafe).is_empty(), "Unsafe states in input"
    goodl = l  # last good overapprox of l

    left, right, P, addtoleft = decompose_literal(l)
    if left is None:
        assert right is None
        return goodl

    EM = getGlobalExprManager()

    def check_literal(lit):
        if lit.isConstant():
            return False
        X = intersection(S, lit)
        if not intersection(X, unsafe).is_empty():
            return False

        r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
        return r.errors is None and r.ready is not None

    def modify_literal(goodl, P, num):
        # FIXME: wbt. overflow?
        left, right = get_left_right(goodl)
        if addtoleft:
            left = EM.Add(left, num)
        else:
            right = EM.Add(right, num)

        # try pushing further
        l = P(left, right)
        if l.isConstant():
            return None
        if l == goodl:  # got nothing new...
            return None
        return l

    print("EXTENDING LITERAL: ", l, goodl)

    bw = left.getType().getBitWidth()
    one = EM.Constant(1, bw)
    two = EM.Constant(2, bw)
    num = EM.Constant(2**(bw-1)-1, bw)

    while True:
        l = modify_literal(goodl, P, num)
        if l is None:
            return goodl

        # push as far as we can with this num
        while check_literal(l):
            goodl = l

            l = modify_literal(goodl, P, num)
            if l is None:
                break

        if num.getValue() <= 1:
            return goodl
        num = EM.Div(num, two)

    assert False, "Unreachable"


def overapprox_clause(n, clauses, executor, L, unsafe, target):
    createSet = executor.getIndExecutor().createStatesSet
    S = createSet()
    c = None
    for i, x in enumerate(clauses):
        if i == n:
            c = x
        else:
            S.intersect(x)
    assert c

    assert intersection(S, unsafe).is_empty(), f"{S} \cap {unsafe}"

    print(f"Overapprox clause: {c}")

    newc = []
    for l in literals(c):
        newl = overapprox_literal(l, S, unsafe, target, executor, L)
        newc.append(newl)
        print(f"  Overapproximated {l} ==> {newl}")

    if len(newc) == 1:
        return newc[0]

    EM = S.get_se_state().getExprManager()
    return EM.conjunction(*newc)


def overapprox(executor, s, unsafeAnnot, seq, L):

    createSet = executor.getIndExecutor().createStatesSet
    S = createSet(s)
    unsafe = createSet(unsafeAnnot)  # safe strengthening
    assert intersection(
        S, unsafe
    ).is_empty(), "Whata? Unsafe states among one-step reachable safe states..."

    print_stdout(f"Overapproximating {S}", color="BROWN")
    print_stdout(f"  with unsafe states: {unsafe}", color="BROWN")
    EM = s.getExprManager()
    target = createSet(seq[-1].toassert())

    expr = S.as_expr().to_cnf()

    clauses = list(expr.children())
    newclauses = clauses.copy()

    # can we drop a clause completely?
   #for c in clauses:
   #    X = createSet(newclauses)
   #    r = check_paths(executor, L.getPaths(), pre=X, post=union(X, target))
   #    if r.errors is None and r.ready:
   #        newclauses.remove(c)
   #        print(f"  dropped {c}...")

    clauses = remove_implied_literals(newclauses, unsafe)
    newclauses = []
    for n in range(0, len(clauses)):
        newclause = overapprox_clause(n, clauses, executor, L, unsafe, target)
        if newclause:
            newclauses.append(newclause)

    clauses = remove_implied_literals(newclauses, unsafe)
    S.reset_expr(EM.conjunction(*clauses))

    sd = S.as_description()
    A1 = AssertAnnotation(sd.getExpr(), sd.getSubstitutions(), EM)
    return InductiveSequence.Frame(S.as_assert_annotation(), None)


class KindSymbolicExecutor(BaseKindSE):
    def __init__(self, prog, ohandler=None, opts=KindSeOptions(), genannot=False):
        super(KindSymbolicExecutor, self).__init__(
            prog=prog, ohandler=ohandler, opts=opts
        )

        self.readypaths = []
        self.stalepaths = []

        self.invpoints = {}
        self.loops = {}

        self.genannot = genannot
        self.sum_loops = {}

    def handle_loop(self, loc, path, states):
        self.loops.setdefault(loc.getBBlockID(), []).append(states)

        assert (
            loc in self.sum_loops[loc.getCFG()]
        ), "Handling a loop that should not be handled"

        # first try to unroll it in the case the loop
        # is easy to verify
        kindse = BaseKindSE(self.getProgram())
        maxk = 5
        dbg_sec("Running nested KindSE")
        res = kindse.run([path.copy()], maxk=maxk)
        dbg_sec()
        if res == 0:
            print_stdout(
                f"Loop {loc.getBBlockID()} proved by the basic KindSE", color="GREEN"
            )
            return True

        assert self.loops.get(loc.getBBlockID())
        if not self.execute_loop(loc, self.loops.get(loc.getBBlockID())):
            self.sum_loops[loc.getCFG()].remove(loc)
            print_stdout(
                f"Falling back to unwinding loop {loc.getBBlockID()}", color="BROWN"
            )
            return False
        return True

    def extend_seq(self, seq, errs0, L):
        S = self.getIndExecutor().createStatesSet(seq[-1].toassert())
        r = check_paths(self, L.getPaths(), post=S)
        if not r.ready:  # cannot step into this frame...
            # FIXME we can use it at least for annotations
            dbg("Infeasible frame...")
            return []

        EM = getGlobalExprManager()
        E = []

        for s in r.ready:
            e = overapprox(self, s, errs0.toassert(), seq, L)
            print_stdout(f"Overapproximated to: {e}", color="BLUE")
            tmp = seq.copy()
            tmp.append(e.states, e.strengthening)
            E.append(tmp)

        return E

    def execute_loop(self, loc, states):
        unsafe = []
        for r in states:
            unsafe += r.errors

        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False  # fall-back to loop unwinding...

        # FIXME: strengthen seq0
        seq0, errs0 = get_initial_seq(unsafe)
        sequences = [seq0]

        print_stdout(f"Executing loop {loc.getBBlockID()} with assumption")
        print_stdout(str(seq0[0]))
        print_stdout(f"and errors : {errs0}")

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- iter ---")
            E = []
            print_stdout(
                f"Got {len(sequences)} abstract paths of loop " f"{loc.getBBlockID()}",
                color="GRAY",
            )
            for seq in sequences:
                print_stdout(f"Processing sequence of len {len(seq)}")
                print("Processing seq:\n", seq)
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.getPaths())
                    assert r.errors is None, "seq is not inductive"

                E += self.extend_seq(seq, errs0, L)
                print(" -- extending DONE --")

            if not E:
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                print("No E")
                return False  # fall-back to unwinding

            # FIXME: check that all the sequences together
            # cover the input paths
            for s, S in ((s, s.toannotation(True)) for s in E):
                if check_inv(self.getProgram(), L, S):
                    print_stdout(
                        f"{S} is inductive on {loc.getBBlock().getID()}", color="BLUE"
                    )
                    if self.genannot:
                        # maybe remember the ind set even without genannot
                        # and use it just for another 'execute_loop'?
                        loc.addAnnotationBefore(s.toannotation().Not(EM))
                    return True
            sequences = E

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
                killed = (
                    (s for s in states.other if s.wasKilled()) if states.other else ()
                )
                for s in killed:
                    self.report(s)
                self.reportfn(f"Inconclusive (init) path: {path}")
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

        killed = (s for s in r.other if s.wasKilled()) if r.other else ()
        for s in killed:
            self.report(s)
            self.reportfn(f"Killed states when executing {path}")
            self.have_problematic_path = True

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

        if __debug__:
            with self.new_output_file(f"{cfg.getFun().getName()}-dfs.dot") as f:
                DFSVisitor().dump(cfg, f)

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        for F in self.callgraph.getFunctions():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            invpoints = self.findInvPoints(cfg)
            self.invpoints[cfg] = invpoints
            self.sum_loops[cfg] = invpoints

            nodes = cfg.getNodes()
            npaths = [AnnotatedCFGPath([n]) for n in nodes if n.hasAssert()]
            step = self.getOptions().step
            while k > 0:
                npaths = [
                    np
                    for p in npaths
                    for np in self.extendPath(
                        p, None, steps=step, atmost=True, stoppoints=invpoints
                    )
                ]
                k -= 1
            paths += npaths

        return paths

    def get_path_to_run(self):
        ready = self.readypaths
        if not ready:
            ready = self.stalepaths
        if ready:
            if len(ready) % 4 == 0:
                # do not run DFS so that we do not starve
                # some path indefinitely, but prefer the
                # lastly added paths...
                ready[-1], ready[0] = ready[0], ready[-1]
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

    def extend_and_queue_paths(self, path, states):
        step = self.getOptions().step
        newpaths = self.extendPath(
            path,
            states,
            steps=step,
            atmost=step != 1,
            stoppoints=self.invpoints[path[0].getCFG()],
        )
        self.queue_paths(newpaths)

    def run(self, paths=None, maxk=None):
        k = 1

        if paths is None:
            paths = self.initializePaths()
        self.queue_paths(paths)

        while True:
            dbg(
                f"Got {len(self.readypaths)} paths ready and {len(self.stalepaths)} waiting"
            )

            path = self.get_path_to_run()
            if path is None:
                if self.have_problematic_path:
                    print_stdout(
                        "Enumerating paths finished, but a problem was met.",
                        color="ORANGE",
                    )
                    return 1

                print_stdout("Enumerating paths done!", color="GREEN")
                return 0

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color="RED")
                return 1
            elif states.errors:  # got error states that may not be real
                assert r is None
                fl = path.first()
                if self.is_inv_loc(fl) and fl in self.sum_loops[fl.getCFG()]:
                    if not self.handle_loop(fl, path, states):
                        # falled-back to unwinding
                        # XXX: could we try again later?
                        self.extend_and_queue_paths(path, states)
                else:
                    # normal path or a loop that we cannot summarize
                    self.extend_and_queue_paths(path, states)

            k += 1
            if maxk and maxk <= k:
                print_stdout(
                    "Hit the maximal number of iterations, giving up.", color="ORANGE"
                )
                return 1
