from itertools import chain
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec, dbgv

from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath, CFG
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions
from .kindsebase import check_paths

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    or_annotations,
)

from slowbeast.symexe.statesset import union, intersection
from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver
from slowbeast.kindse.kindse.relations import get_subs

from .loops import SimpleLoop
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence
from .overapproximations import remove_implied_literals, overapprox_set


def get_initial_seq2(unsafe, path, L):
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
    E = None  # unsafe states

    EM = getGlobalExprManager()
    Or, conjunction = EM.Or, EM.conjunction
    for u in unsafe:
        uconstr = u.getConstraints()
        E = Or(conjunction(*uconstr), E) if E else conjunction(*uconstr)

    S = EM.Not(E)

    # simplify the formulas
    if not S.is_concrete():
        S = conjunction(*remove_implied_literals(S.to_cnf().children()))
    if not E.is_concrete():
        E = conjunction(*remove_implied_literals(E.to_cnf().children()))

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, None), InductiveSequence.Frame(Se, None)


def get_initial_seq(unsafe, path, L):
    """
    Return two annotations, one that is the initial safe sequence
    and one that represents the error states.
    This implementation returns not the weakest sets, but stronger sets
    that should be easier to prove (and then we can prove the remaining
    states safe in another iteration).
    """

    # NOTE: Only safe states that reach the assert are not inductive on the
    # loop header -- what we need is to have safe states that already left
    # the loop and safely pass assertion or avoid it.
    # These are the complement of error states intersected with the
    # negation of loop condition.

    S = None  # safe states
    E = None  # unsafe states

    EM = getGlobalExprManager()
    Not, conjunction = EM.Not, EM.conjunction
    for u in unsafe:
        # add constraints without loop exit condition
        # (we'll add the loop condition later)
        uconstr = u.getConstraints()
        if not uconstr:
            S = EM.getFalse()
            E = EM.getTrue()
            break  # nothing we can do...
        # all constr. apart from the last one
        pc = conjunction(*uconstr[:-1])
        # last constraint is the failed assertion
        S = conjunction(pc, Not(uconstr[-1]), S) if S else EM.And(pc, Not(uconstr[-1]))
        # unsafe states
        E = EM.Or(conjunction(*uconstr), E) if E else conjunction(*uconstr)

    # simplify the formulas
    if not S.is_concrete():
        S = conjunction(*remove_implied_literals(S.to_cnf().children()))
    if not E.is_concrete():
        E = conjunction(*remove_implied_literals(E.to_cnf().children()))

    subs = {l: l.load for l in unsafe[0].getNondetLoads()}
    Sa = AssertAnnotation(S, subs, EM)
    Se = AssertAnnotation(E, subs, EM)

    return InductiveSequence(Sa, None), InductiveSequence.Frame(Se, None)

def overapprox(executor, s, unsafeAnnot, seq, L):
    S = executor.getIndExecutor().createStatesSet(s)
    EM = s.getExprManager()
    return overapprox_set(executor, EM, S, unsafeAnnot, seq, L)

def simplify_expr(expr, EM):
    return EM.conjunction(*remove_implied_literals(expr.to_cnf().children()))


class KindSEChecker(BaseKindSE):
    """
    An executor that recursively checks the validity of a one particular assertion.
    It inherits from BaseKindSE to have the capabilities to execute paths.
    """

    def __init__(self, toplevel_executor, loc, A):
        super().__init__(toplevel_executor.getProgram(),
                         ohandler=None,
                         opts=toplevel_executor.getOptions(),
                         programstructure=toplevel_executor.programstructure)
        self.location = loc
        self.assertion = A
        self.toplevel_executor = toplevel_executor

        self.readypaths = []
        self.stalepaths = []

        cfg = loc.getCFG()
        self.no_sum_loops = set()

    def check_loop_precondition(self, L, A):
        loc = L.header()
        dbg_sec(f"Checking if {A} holds on loc {loc.getBBlock().get_id()}")

       # def reportfn(msg, *args, **kwargs):
       #     print_stdout(f"> {msg}", *args, **kwargs)

        checker = KindSEChecker(self.toplevel_executor, loc, A)
        result, states = checker.check()
        dbg_sec()
        return result, states


    def handle_loop(self, loc, path, states):
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

        # first try to unroll it in the case the loop is easy to verify
       #kindse = BaseKindSE(self.getProgram())
       #maxk = 15
       #dbg_sec("Running nested KindSE")
       #res = kindse.run([path.copy()], maxk=maxk)
       #dbg_sec()
       #if res is Result.SAFE:
       #    print_stdout(
       #        f"Loop {loc.getBBlockID()} proved by unwinding", color="GREEN"
       #    )
       #    return res
       #FIXME: uncomment and return the states
       #elif res is Result.UNSAFE:
       #    return res # found an error

        if self.execute_loop(path, loc, states):
            return Result.SAFE

        self.no_sum_loops.add(loc)
        print_stdout(
            f"Falling back to unwinding loop {loc.getBBlockID()}", color="BROWN"
        )
        return Result.UNKNOWN

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
            if e == seq[-1]:
                dbg("Did not extend (got the same elem...)")
                continue
            print_stdout(f"Extended with: {e}", color="BROWN")
            tmp = seq.copy()
            tmp.append(e.states, e.strengthening)

            if __debug__:
                r = tmp.check_ind_on_paths(self, L.getPaths())
                assert (
                    r.errors is None
                ), f"Extended sequence is not inductive (CTI: {r.errors[0].model()})"

            E.append(tmp)

        return E

    def abstract_seq(self, seq, errs0, L):
        # don't try with short sequences
        if len(seq) < 5:
            return seq

        # try to merge last two frames
        assert len(seq) >= 2
        A1 = seq[-1].toassume()
        A2 = seq[-2].toassume()
        e1 = A1.getExpr().to_cnf()
        e2 = A2.getExpr().to_cnf()

        C1 = set(e1.children())
        C = set()
        N1 = set()
        N2 = set()
        for c in e2.children():
            if c in C1:
                C.add(c)
            else:
                N2.add(c)
        for c in C1:
            if c not in C:
                N1.add(c)

        if not C:
            return seq

        # replace last two frames with one merged frame
        EM = getGlobalExprManager()
        seq.pop()

        seq[-1].states = AssertAnnotation(EM.conjunction(*C), A1.getSubstitutions(), EM)
        S1 = AssertAnnotation(EM.conjunction(*N1), A1.getSubstitutions(), EM)
        S2 = AssertAnnotation(EM.conjunction(*N2), A2.getSubstitutions(), EM)
        seq[-1].strengthening = or_annotations(EM, True, S1, S2)

        # FIXME: we are still precies, use abstraction here...
        return seq

    def overapprox_init_seq(self, seq0, errs0, L):
        if __debug__:
            r = seq0.check_ind_on_paths(self, L.getPaths())
            assert r.errors is None, "seq is not inductive"
        S = self.getIndExecutor().createStatesSet(seq0.toannotation(True))
        EM = getGlobalExprManager()
        seq = InductiveSequence(
            overapprox_set(self, EM, S, errs0.toassert(), seq0, L).toassert()
        )
        r = seq.check_ind_on_paths(self, L.getPaths())
        # Why could this happen?
        if r.errors is None and r.ready:
            return seq
        return seq0

    def strengthen_initial_seq(self, seq0, errs0, path, L: SimpleLoop):
        # NOTE: if we would pass states here we would safe some work.. be it would be less generic
        r = seq0.check_ind_on_paths(self, L.getPaths())
        # catch it in debug mode so that we can improve...
        # assert r.errors is None, f"Initial seq is not inductive: {seq0}"
        if r.errors is None:
            dbg("Initial sequence is inductive", color="dark_green")
            return seq0

        dbg("Initial sequence is NOT inductive, trying to fix it", color="wine")
        # is the assertion inside the loop or after the loop?
        EM = getGlobalExprManager()
        assert path[0] == L._header
        createSet = self.getIndExecutor().createStatesSet
        if (path[0], path[1]) in L.get_inedges():
            # FIXME: we actually do not use the concrete assertion at all right now...
            # assertion is inside, evaluate the jump-out instruction
            # get the safe states that jump out of the loop after one iteration
            r = check_paths(self, L.getPaths())
            if not r.ready:
                return None
            ready = [
                s
                for s in r.ready
                if s.pc in (e[1].getBBlock().first() for e in L.getExits())
            ]
            if not ready:
                return None
            R = createSet()
            # FIXME: we can use only a subset of the states, wouldn't that be better?
            for r in ready:
                # do not use the first constraint -- it is the inedge condition that we want to ignore,
                # because we want to jump out of the loop (otherwise we will not get inductive set)
                C = r.getConstraints()[1:]
                expr = EM.conjunction(*C)
                expr = EM.conjunction(
                    *remove_implied_literals(expr.to_cnf().children())
                )
                tmp = createSet(r)
                tmp.reset_expr(expr)
                R.add(tmp)
            seq0 = InductiveSequence(R.as_assert_annotation())
            r = seq0.check_ind_on_paths(self, L.getPaths())
            # this may mean that the assertion in fact does not hold
            # assert r.errors is None, f"SEQ not inductive, but should be. CTI: {r.errors[0].model()}"
        else:
            r = check_paths(self, [AnnotatedCFGPath([path[0]])])
            if r.ready is None:
                return None
            R = createSet()
            ready = [s for s in r.ready if s.pc is path[1].getBBlock().first()]
            for r in ready:
                R.add(r)
            R.intersect(seq0.toannotation(True))
            seq0 = InductiveSequence(R.as_assert_annotation())
            r = seq0.check_ind_on_paths(self, L.getPaths())
            # this may mean that the assertion in fact does not hold
            # assert r.errors is None, f"SEQ not inductive, but should be. CTI: {r.errors[0].model()}"

        r = seq0.check_ind_on_paths(self, L.getPaths())
        if r.errors is None:
            dbg("Initial sequence made inductive", color="dark_green")
            return seq0
        return None

    def execute_loop(self, path, loc, states):
        dbgv(f"========== Executing loop {loc.getBBlockID()} ===========")
        unsafe = states.errors
        assert unsafe, "No unsafe states, we should not get here at all"

        L = SimpleLoop.construct(loc)
        if L is None:
            return False  # fall-back to loop unwinding...

        dbgv(f"Getting initial sequence for loop {loc.getBBlockID()}")
        seq0, errs0 = get_initial_seq(unsafe, path, L)
        # the initial sequence may not be inductive (usually when the assertion
        # is inside the loop, so we must strenghten it
        dbgv(f"Strengthening the initial sequence")
        seq0 = self.strengthen_initial_seq(seq0, errs0, path, L)
        if seq0 is None:
            return False  # we failed...

        dbgv(f"Overapproximating the initial sequence")
        seq0 = self.overapprox_init_seq(seq0, errs0, L)
        assert seq0

        sequences = [seq0]

        print_stdout(
            f"Executing loop {loc.getBBlockID()} with assumption", color="white"
        )
        print_stdout(str(seq0[0]), color="white")
        print_stdout(f"and errors : {errs0}")

        # NOTE: we do not require the initial (target) set to be inductive!,
        # only the rest of the sequence is inductive and it implies the target set

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- extending sequences ---")
            print_stdout(
                f"Got {len(sequences)} abstract path(s) of loop " f"{loc.getBBlockID()}",
                color="GRAY",
            )

            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for s, S in ((s, s.toannotation(True)) for s in sequences):
                res, _ = self.check_loop_precondition(L, S)
                if res is Result.SAFE:
                    print_stdout(
                        f"{S} holds on {loc.getBBlock().get_id()}", color="BLUE"
                    )
                   #if self.genannot:
                   #    # maybe remember the ind set even without genannot
                   #    # and use it just for another 'execute_loop'?
                   #    loc.addAnnotationBefore(s.toannotation().Not(EM))
                    return True

            extended = []
            for seq in sequences:
                print_stdout(
                    f"Processing sequence of len {len(seq)}:\n{seq}", color="dark_blue"
                )
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.getPaths())
                    assert r.errors is None, "seq is not inductive"

                for e in self.extend_seq(seq, errs0, L):
                    extended.append(self.abstract_seq(e, errs0, L))
                # print(" -- extending DONE --")

            if not extended:
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                print_stdout("Failed extending any sequence", color="orange")
                return False  # fall-back to unwinding

            sequences = extended

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
                killed1 = (
                    (s for s in states.other if s.wasKilled()) if states.other else ()
                )
                killed2 = (
                    (s for s in states.early if s.wasKilled()) if states.early else ()
                )
                for s in chain(killed1, killed2):
                    self.report(s, self.reportfn)
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

        killed1 = (s for s in r.other if s.wasKilled()) if r.other else ()
        killed2 = (s for s in r.early if s.wasKilled() or (s.hasError() and
                                                           s.getError().isMemError())) if r.early else ()
        problem = False
        for s in chain(killed1, killed2):
            problem = True
            self.report(s, fn=self.reportfn)
            self.reportfn(f"Killed states when executing {path}")
            self.have_problematic_path = True

        if r.errors:
            self.reportfn(f"Possibly error path: {path}", color="ORANGE")
        elif problem:
            self.reportfn(f"Problem path: {path}", color="PURPLE")
        else:
            self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        return None, r

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

    def is_loop_header(self, loc):
        assert isinstance(loc, CFG.AnnotatedNode), loc
        return loc in self.programstructure.get_loop_headers(loc.getCFG())

    def queue_paths(self, paths):
        is_loop_header = self.is_loop_header
        for p in paths:
            if is_loop_header(p.first()):
                self.stalepaths.append(p)
            else:
                self.readypaths.append(p)

    def extend_and_queue_paths(self, path, states):
        step = self.getOptions().step
        invpoints = self.programstructure.get_loop_headers(path[0].getCFG())
        newpaths = self.extendPath(
            path,
            states,
            steps=step,
            atmost=step != 1,
            stoppoints=invpoints,
        )

        self.queue_paths(newpaths)

    def check(self):
        # the initial error path that we check
        loc = self.location
        path = AnnotatedCFGPath([loc])
        path.addLocAnnotationBefore(self.assertion, loc)
        self.extend_and_queue_paths(path, states=None)

        problem_states = []
        while True:
            path = self.get_path_to_run()
            if path is None:
                return Result.UNKNOWN if problem_states else Result.SAFE, problem_states

            r, states = self.check_path(path)
            if r is Result.UNSAFE:
                return r, states
            elif states.errors:  # got error states that may not be real
                assert r is None
                fl = path.first()
                if fl not in self.no_sum_loops and self.is_loop_header(fl):
                    res = self.handle_loop(fl, path, states)
                    if res is Result.UNSAFE:
                        raise NotImplementedError("We do not return the states here...")
                        return res, None
                    elif res is Result.UNKNOWN:
                        # falled-back to unwinding
                        # XXX: could we try again later?
                        self.extend_and_queue_paths(path, states)
                    else:
                        assert res is Result.SAFE
                        dbg(f"Path with loop {fl.getBBlockID()} proved safe", color="dark_green")
                else:
                    # normal path or a loop that we cannot summarize
                    self.extend_and_queue_paths(path, states)
            else:
                dbg(f"Safe path: {path}")

        raise RuntimeError("Unreachable")


class KindSymbolicExecutor(BaseKindSE):
    """
    The main class for KindSE that divides and conquers the tasks.
    It inherits from BaseKindSE to have program structure and such,
    TODO but we should change that, build program structure here,
    and keep BaseKindSE a class that just takes care for executing paths.
    """

    def __init__(self, prog, ohandler=None, opts=KindSeOptions(), genannot=False):
        super().__init__(
            prog=prog, ohandler=ohandler, opts=opts
        )

    def _get_error_paths(self):
        paths = []
        # initialize the paths only in functions
        # that are reachable in the callgraph
        for F in self.programstructure.callgraph.funs():
            if F.isUndefined():
                continue

            cfg = self.getCFG(F)
            nodes = cfg.getNodes()
            paths.extend(AnnotatedCFGPath([n]) for n in nodes if n.hasAssert())

        return paths

    def _get_possible_errors(self):
        for err in self._get_error_paths():
            assert len(err) == 1
            r = check_paths(self, [err])
            assert r.errors, "The error path has no errors"
            for e in r.errors:
                yield err[0], AssertAnnotation(e.path_condition(), get_subs(e), e.getExprManager())

    def run(self):
        has_unknown = False
        for loc, A in self._get_possible_errors():
            dbg(f"Checking possible error: {A.getExpr()} @ {loc}")
            checker = KindSEChecker(self, loc, A)
            result, states = checker.check()
            if result is Result.UNSAFE:
                assert states.errors, "No errors in unsafe result"
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color="red")
                return result
            elif result is Result.SAFE:
                print_stdout(f"Error condition {A.getExpr()} at {loc.getBBlockID()} is safe!.", color="green")
            elif result is Result.UNKNOWN:
                print_stdout(f"Checking assert {A} at {loc.getBBlockID()} was unsuccessful.", color="orange")
                has_unknown = True

        return Result.UNKNOWN if has_unknown else Result.SAFE
