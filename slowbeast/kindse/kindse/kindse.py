from itertools import chain
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec, dbgv, ldbgv

from slowbeast.ir.instruction import Assert as AssertInst
from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions
from .kindsebase import check_paths
from slowbeast.symexe.statesset import intersection, union

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    or_annotations,
)

from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver

from .loops import SimpleLoop
from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence
from .overapproximations import remove_implied_literals, overapprox_set
from .relations import get_safe_relations


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
    create_set = executor.ind_executor().create_states_set
    target = create_set(seq[-1].toassert())
    S = create_set(s)
    for rel in get_safe_relations([s], None):
        ldbgv("  Adding relation {0}", (rel,))
        S.intersect(rel)
    EM = s.expr_manager()
    return overapprox_set(executor, EM, S, unsafeAnnot, target, L)


def simplify_expr(expr, EM):
    return EM.conjunction(*remove_implied_literals(expr.to_cnf().children()))


class KindSEChecker(BaseKindSE):
    """
    An executor that recursively checks the validity of one particular assertion.
    It inherits from BaseKindSE to have the capabilities to execute paths.
    """

    def __init__(self, toplevel_executor, loc, A):
        super().__init__(
            toplevel_executor.getProgram(),
            ohandler=None,
            opts=toplevel_executor.getOptions(),
            programstructure=toplevel_executor.programstructure,
        )
        self.location = loc
        self.assertion = A
        self.toplevel_executor = toplevel_executor

        # paths to still search
        self.readypaths = []
        # invariant sets that we generated
        self.inductive_sets = {}

        self.no_sum_loops = set()

    def unfinished_paths(self):
        return self.readypaths

    def check_loop_precondition(self, L, A):
        loc = L.header()
        dbg_sec(f"Checking if {A} holds on {loc}")

        # def reportfn(msg, *args, **kwargs):
        #     print_stdout(f"> {msg}", *args, **kwargs)

        checker = KindSEChecker(self.toplevel_executor, loc, A)
        result, states = checker.check(L.entries())
        dbg_sec()
        return result, states

    def handle_loop(self, loc, path, states):
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

    #   # first try to unroll it in the case the loop is easy to verify
    #   kindse = BaseKindSE(self.getProgram())
    #   maxk = 15
    #   dbg_sec("Running nested KindSE")
    #   res = kindse.run([path.copy()], maxk=maxk)
    #   dbg_sec()
    #   if res is Result.SAFE:
    #      print_stdout(
    #          f"Loop {loc} proved by unwinding", color="GREEN"
    #      )
    #      return res, []
    #   # FIXME: uncomment and return the states
    #   elif res is Result.UNSAFE:
    #      self.no_sum_loops.add(loc)
    #      return res, [path]  # found an error

        L = SimpleLoop.construct(loc)
        if L is None:
            print_stdout("Was not able to construct the loop info")
            print_stdout(f"Falling back to unwinding loop {loc}", color="BROWN")
            self.no_sum_loops.add(loc)
            return Result.UNKNOWN, self.extend_paths(path, None)

        if self.fold_loop(path, loc, L, states):
            return Result.SAFE, []
        else:
            return self.unfold_loop(path, loc)

    def unfold_loop(self, path, loc):
        """
        Take path and loop for which we failed to create an invariant and unwind the loop as far as we can
        such that we avoid the safe sets that we computed.
        """
        # unwind the paths and check subsumption
        paths = self.extend_paths(path, None)
        inductive_sets = self.inductive_sets.get(loc)
        if not inductive_sets:
            return Result.UNKNOWN, paths

        finalpaths = []
        newpaths = []
        create_set = self.ind_executor().create_states_set
        # fixme: the state inside set should use incremental solver to speed-up solving... after all, it is a place
        # where we add formulas monotonically.
        I = create_set(union(inductive_sets))
        assert not I.is_empty()
        I.complement()
       #solver = IncrementalSolver()
       #solver.add(I.expr())

        while paths:
            dbg("Next iteration of unfolding the loop...")
            for p in paths:
                r, states = self.check_path(p)
                if r is Result.UNSAFE:
                    # we hit real unsafe path - return it so that the main executor
                    # will re-execute it and report
                    if __debug__:
                        tmp = create_set(states.errors[0])
                        assert intersection(I, tmp).is_empty(), "Error state is subsumed..."
                    return Result.UNSAFE, [p]
                # otherwise just prolong the paths that failed the induction step
                # and that are not subsumed
                assert states.errors is None or len(states.errors) == 1
                errst = states.errors[0] if states.errors else None
                if errst:
                    tmp = create_set(errst)
                    if not intersection(I, tmp).is_empty():
                        # not subsumed
                        # FIXME: some overapproximation of the complement of the intersection and add it to the path
                        finalpaths.append(p)
                    else:
                        # errst is subsumed and subsumed paths need to be prolonged
                        newpaths += self.extend_paths(p, None)
            paths = newpaths

        # TODO: we could return SAFE when finalpaths is empty
        return Result.UNKNOWN, finalpaths

    def extend_seq(self, seq, errs0, L):
        S = self.ind_executor().create_states_set(seq[-1].toassert())
        r = check_paths(self, L.paths(), post=S)
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
                r = tmp.check_ind_on_paths(self, L.paths())
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
        e1 = A1.expr().to_cnf()
        e2 = A2.expr().to_cnf()

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

        seq[-1].states = AssertAnnotation(EM.conjunction(*C), A1.substitutions(), EM)
        S1 = AssertAnnotation(EM.conjunction(*N1), A1.substitutions(), EM)
        S2 = AssertAnnotation(EM.conjunction(*N2), A2.substitutions(), EM)
        seq[-1].strengthening = or_annotations(EM, True, S1, S2)

        # FIXME: we are still precies, use abstraction here...
        return seq

    def overapprox_init_seq(self, seq0, errs0, L):
        if __debug__:
            r = seq0.check_ind_on_paths(self, L.paths())
            assert r.errors is None, "seq is not inductive"
        create_set = self.ind_executor().create_states_set
        target = create_set(seq0[-1].toassert())
        S = create_set(seq0.toannotation(True))
        EM = getGlobalExprManager()
        seq = InductiveSequence(
            overapprox_set(self, EM, S, errs0.toassert(), target, L).toassert()
        )
        r = seq.check_ind_on_paths(self, L.paths())
        # Why could this happen?
        if r.errors is None and r.ready:
            return seq
        return seq0

    def strengthen_initial_seq_picking(self, seq0, errs0, path, L: SimpleLoop):
        # try to pick some inductive subset
 
        F = seq0.toannotation(True)
        expr = F.expr()
        EM = getGlobalExprManager()
        R = self.ind_executor().create_states_set(F)
        R.reset_expr() # clear the state but preserve substitutions
        T = R.copy()

        for c in expr.to_cnf().children():
            tmpset = T.copy()
            tmpset.intersect(c)
            tmp = InductiveSequence(tmpset.as_assert_annotation())
            print('tmp', tmp)
            r = tmp.check_ind_on_paths(self, L.paths())
            if r.errors is None:
                print('INDUCTIVE', c)
                R.intersect(c)
            else:
                print(f"Not inductive (CTI: {r.errors[0].model()})")

        print(R)
        seq0 = InductiveSequence(R.as_assert_annotation())

        #dbg("Initial sequence made inductive", color="dark_green")
        ## dropping the clauses failed
        r = seq0.check_ind_on_paths(self, L.paths())
        if r.errors is None:
            dbg("Initial sequence made inductive", color="dark_green")
            return seq0
 
        assert False
        return None

    def strengthen_initial_seq_exit_cond(self, seq0, errs0, path, L: SimpleLoop):
        """ Strengthen the initial sequence through loop entry condition.
            Does not work for assertions inside the loop
        """
        # get the prefix of the path that exits the loop
        prefix = None
        exits = L.exits()
        for n in range(len(path)):
            if path[n] in exits:
                prefix = AnnotatedCFAPath(path.edges()[: n + 1])
                break
        if prefix is None:
            return None
        #assert prefix, "Failed getting loop-exit condition"
        r = check_paths(self, [prefix])
        ready = r.ready
        if ready is None:
            return None
        R = self.ind_executor().create_states_set()
        R.add(ready)
        R.intersect(seq0.toannotation(True))
        if R.is_empty():
            # empty initial set is wrong, it probably means that
            # the assertion is inside the loop and we added
            # contradicting exit condition
            return None
        seq0 = InductiveSequence(R.as_assert_annotation())
        # this may mean that the assertion in fact does not hold
        r = seq0.check_ind_on_paths(self, L.paths())
        if r.errors is None:
            return seq0
        return None

    def strengthen_initial_seq_loop_iter(self, seq0, errs0, path, L: SimpleLoop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """
        # get the safe states that jump out of the loop after one iteration
        r = check_paths(self, L.get_exit_paths())
        ready = r.ready
        if not ready:
            return None
        create_set = self.ind_executor().create_states_set
        R = create_set()
        # FIXME: we can use only a subset of the states, wouldn't that be better?
        EM = getGlobalExprManager()
        for r in ready:
            # do not use the first constraint -- it is the inedge condition that we want to ignore,
            # because we want to jump out of the loop (otherwise we will not get inductive set)
            C = r.getConstraints()[1:]
            expr = EM.conjunction(*C)
            expr = EM.conjunction(
                *remove_implied_literals(expr.to_cnf().children())
            )
            tmp = create_set(r)
            tmp.reset_expr(expr)
            R.add(tmp)

       #expr = R.as_expr()
       #S = overapprox_set(self, EM, R, errs0.toassert(), seq0.toannotation(),
       #                   L, drop_only=True)
       #seq0 = InductiveSequence(S.toassert())
        seq0 = InductiveSequence(R.as_assert_annotation())
        # this may mean that the assertion in fact does not hold
        r = seq0.check_ind_on_paths(self, L.paths())
        if r.errors is None:
            return seq0
        return None


    def strengthen_initial_seq(self, seq0, errs0, path, L: SimpleLoop):
        # NOTE: if we would pass states here we would safe some work.. be it would be less generic
        assert path[0].source() is L.header()
        r = seq0.check_ind_on_paths(self, L.paths())
        if r.errors is None:
            dbg("Initial sequence is inductive", color="dark_green")
            return seq0

        dbg("Initial sequence is NOT inductive, trying to fix it", color="wine")
        dbg(str(seq0))

        tmp = self.strengthen_initial_seq_exit_cond(seq0, errs0, path, L)
        if tmp:
            dbg("Succeeded strengthening the initial sequence with exit condition")
            return tmp
        dbg("Failed strengthening the initial sequence with exit condition")

       #tmp = self.strengthen_initial_seq_picking(seq0, errs0, path, L)
       #if tmp:
       #    return tmp
       #dbg("Failed strengthening the initial sequence with picking")

        tmp = self.strengthen_initial_seq_loop_iter(seq0, errs0, path, L)
        if tmp:
            dbg("Succeeded strengthening the initial sequence with last iteration")
            ## FIXME: overapprox & drop
            return tmp
        dbg("Failed strengthening the initial sequence with last iteration")

        dbg("-- Failed making the initial sequence inductive --")
        return None

    def fold_loop(self, path, loc, L : SimpleLoop, states):
        dbg(f"========== Folding loop {loc} ===========")
        unsafe = states.errors
        assert unsafe, "No unsafe states, we should not get here at all"

        dbgv(f"Getting initial sequence for loop {loc}")
        seq0, errs0 = get_initial_seq(unsafe, path, L)
        # the initial sequence may not be inductive (usually when the assertion
        # is inside the loop, so we must strenghten it
        dbg(f"Strengthening the initial sequence")
        seq0 = self.strengthen_initial_seq(seq0, errs0, path, L)
        if seq0 is None:
            return False  # we failed...

        dbgv(f"Overapproximating the initial sequence")
        seq0 = self.overapprox_init_seq(seq0, errs0, L)
        assert seq0

        sequences = [seq0]

        print_stdout(f"Executing loop {loc} with assumption", color="white")
        print_stdout(str(seq0[0]), color="white")
        print_stdout(f"and errors : {errs0}")

        # NOTE: we do not require the initial (target) set to be inductive!,
        # only the rest of the sequence is inductive and it implies the target set

        # print('--- starting building sequences  ---')
        EM = getGlobalExprManager()
        while True:
            print("--- extending sequences ---")
            print_stdout(
                f"Got {len(sequences)} abstract path(s) of loop " f"{loc}",
                color="GRAY",
            )

            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for s, S in ((s, s.toannotation(True)) for s in sequences):
                res, _ = self.check_loop_precondition(L, S)
                if res is Result.SAFE:
                    print_stdout(f"{S} holds on {loc}", color="BLUE")
                    # if self.genannot:
                    #    # maybe remember the ind set even without genannot
                    #    # and use it just for another 'fold_loop'?
                    #    loc.addAnnotationBefore(s.toannotation().Not(EM))
                    return True

            extended = []
            for seq in sequences:
                print_stdout(
                    f"Processing sequence of len {len(seq)}:\n{seq}", color="dark_blue"
                )
                if __debug__:
                    r = seq.check_ind_on_paths(self, L.paths())
                    assert r.errors is None, "seq is not inductive"

                dbg("Extending the sequence")
                for e in self.extend_seq(seq, errs0, L):
                    extended.append(self.abstract_seq(e, errs0, L))
                dbg("Extending the sequence finished")

            if not extended:
                dbg("Failed extending any sequence")
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                print_stdout("Failed extending any sequence", color="orange")
                # store the generated sequences, we will use them during unfolding
                # and when we reach the loop again
                create_set = self.ind_executor().create_states_set
                self.inductive_sets.setdefault(loc, []).extend((create_set(s.toannotation()) for s in sequences))
                return False  # fall-back to unwinding

            sequences = extended

    def check_path(self, path):
        first_loc = path[0]
        if self._is_init(first_loc.source()):
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
        killed2 = (
            (
                s
                for s in r.early
                if s.wasKilled() or (s.hasError() and s.getError().isMemError())
            )
            if r.early
            else ()
        )
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
        if ready:
            if len(ready) % 4 == 0:
                # do not run DFS so that we do not starve
                # some path indefinitely, but prefer the
                # lastly added paths...
                ready[-1], ready[0] = ready[0], ready[-1]
            return ready.pop()
        return None

    def is_loop_header(self, loc):
        return loc in self.programstructure.get_loop_headers()

    def queue_paths(self, paths):
        assert isinstance(paths, list), paths
        self.readypaths.extend(paths)

    def extend_paths(self, path, states):
        step = self.getOptions().step
        invpoints = self.programstructure.get_loop_headers()
        return self.extend_path(
            path,
            states,
            steps=step,
            atmost=step != 1,
            stoppoints=invpoints,
        )

    def extend_and_queue_paths(self, path, states):
        self.queue_paths(self.extend_paths(path, states))

    def check(self, onlyedges=None):
        # the initial error path that we check
        loc = self.location
        for edge in onlyedges if onlyedges else loc.predecessors():
            path = AnnotatedCFAPath([edge])
            path.add_annot_after(self.assertion)
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
                # is this a path starting at a loop header?
                fl = path[0].source()
                if fl not in self.no_sum_loops and self.is_loop_header(fl):
                    res, newpaths = self.handle_loop(fl, path, states)
                    if res is Result.SAFE:
                        assert not newpaths
                        dbg(f"Path with loop {fl} proved safe", color="dark_green")
                    else:
                        assert newpaths, newpaths
                        self.queue_paths(newpaths)
                else:
                    # normal path or a loop that we cannot summarize
                    self.extend_and_queue_paths(path, states)
            else:
                dbg(f"Safe path: {path}")

        raise RuntimeError("Unreachable")


def edge_has_assert(edge):
    return any(map(lambda i: isinstance(i, AssertInst), edge))


class KindSymbolicExecutor(BaseKindSE):
    """
    The main class for KindSE that divides and conquers the tasks.
    It inherits from BaseKindSE to have program structure and such,
    TODO but we should change that, build program structure here,
    and keep BaseKindSE a class that just takes care for executing paths.
    """

    def __init__(self, prog, ohandler=None, opts=KindSeOptions()):
        super().__init__(prog=prog, ohandler=ohandler, opts=opts)

   #def _get_error_paths(self):
   #    paths = []
   #    # initialize the paths only in functions
   #    # that are reachable in the callgraph
   #    for F in self.programstructure.callgraph.funs():
   #        if F.isUndefined():
   #            continue

   #        cfa = self.get_cfa(F)
   #        locs = cfa.locations()
   #        iserr = cfa.is_err
   #        paths.extend(AnnotatedCFAPath([edge]) for l in locs for edge in l.predecessors() if iserr(l))

   #    return paths

   #def _get_possible_errors(self):
       #for err in self._get_error_paths():
       #    assert len(err) == 1
       #    r = check_paths(self, [err])
       #    assert r.errors, "The error path has no errors"
       #    for e in r.errors:
       #        EM = e.expr_manager()
       #        yield err[0].source(), AssertAnnotation(
       #            EM.Not(e.path_condition()), get_subs(e), EM
       #        )
    def _get_possible_errors(self):
        EM = getGlobalExprManager()
        for F in self.programstructure.callgraph.funs():
            if F.isUndefined():
                continue

            cfa = self.get_cfa(F)
            locs = cfa.locations()
            iserr = cfa.is_err

            for l in locs:
                if iserr(l):
                    yield l, AssertAnnotation(EM.getFalse(), {}, EM)

    def run(self):
        has_unknown = False
        for loc, A in self._get_possible_errors():
            print_stdout(f"Checking possible error: {A.expr()} @ {loc}", color="white")
            checker = KindSEChecker(self, loc, A)
            result, states = checker.check()
            if result is Result.UNSAFE:
                assert states.errors, "No errors in unsafe result"
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color="red")
                return result
            elif result is Result.SAFE:
                print_stdout(
                    f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                )
            elif result is Result.UNKNOWN:
                print_stdout(
                    f"Checking assert {A} at {loc} was unsuccessful.", color="orange"
                )
                has_unknown = True

        return Result.UNKNOWN if has_unknown else Result.SAFE
