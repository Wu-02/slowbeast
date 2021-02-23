from heapq import heappush, heappop
from itertools import chain
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec, dbgv, ldbgv, ldbg

from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions
from slowbeast.symexe.statesset import intersection, union, complement, StatesSet
from slowbeast.analysis.loops import Loop

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    state_to_annotation
)

from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver

from .kindsebase import check_paths, KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence
from .overapproximations import remove_implied_literals, overapprox_set
from .relations import get_safe_relations


def _dump_inductive_sets(checker, loc):
    dbg(f"With this INVARIANT set at loc {loc}:", color="dark_green")
    IS = checker.invariant_sets.get(loc)
    if IS:
        dbg(f"\n{IS}", color="dark_green")
    else:
        dbg(" ∅", color="dark_green")
    dbg(f"With this INDUCTIVE set at loc {loc}:", color="dark_green")
    IS = checker.inductive_sets.get(loc)
    if IS:
        dbg(f"\n{IS}", color="dark_green")
    else:
        dbg(" ∅", color="dark_green")



def overapprox(executor, s, E, target, L):
    S = executor.create_set(s)

    # FIXME: this is a workaround until we support nondet() calls in lazy execution
    r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
    if r.errors:
        dbg(
            "FIXME: pre-image is not inductive cause we do not support nondets() in lazy execution yet"
        )
        return None
    # --- workaround ends here...

    # if __debug__:
    #    r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
    #    if r.errors:
    #        print(r.errors[0].path_condition())
    #    assert (
    #        r.errors is None
    #        ), f"Pre-image with sequence is not inductive\n"\
    #           f"-- pre-image --:\n{S}\n"\
    #           f"-- target --:\n{target}\n"\
    #           f"-- error states --:\n{r.errors[0].path_condition()}\n"\
    #           f"-- CTI: --\n{r.errors[0].model()}"

    assert not S.is_empty(), "Infeasible states given to overapproximate"
    S.reset_expr(S.as_expr().rewrite_and_simplify())
    for rel in get_safe_relations([s], unsafe=None, prevsafe=target):
        ldbgv("  Adding relation {0}", (rel,))
        S.intersect(rel)
        assert not S.is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            S, E
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

    return overapprox_set(executor, s.expr_manager(), S, E, target, L)


def is_seq_inductive(seq, target, executor, L, has_ready=False):
    r = seq.check_ind_on_paths(executor, L.paths(), target)
    for s in r.killed():
        dbg("Killed a state")
        executor.report(s)
        return False
    return r.errors is None and (r.ready or not has_ready)


def strip_first_assume_edge(path: AnnotatedCFAPath):
    idx = path.first_assume_edge_idx()
    # we use this func only on loop edges, so it must contain the entry condition
    assert idx is not None and idx + 1 < len(path)
    return path.subpath(idx + 1)

def strip_last_assume_edge(path: AnnotatedCFAPath):
    idx = path.last_assume_edge_idx()
    # we use this func only on loop edges, so it must contain the entry condition
    assert idx is not None and idx + 1 < len(path)
    return path.subpath(0, idx - 1)

def postcondition_expr(s):
    return state_to_annotation(s).do_substitutions(s)

class InductiveSet:
    """
    Class representing an inductive set that we derive for a loop header.
    """

    def __init__(self, initial_set: StatesSet = None):
        assert initial_set is None or isinstance(initial_set, StatesSet)
        if initial_set:
            self.I = initial_set
            cI = IncrementalSolver()
            cI.add(complement(initial_set).as_expr())
            self.cI = cI
            # track all added sets
            self.sets = [initial_set]
        else:
            self.I = None
            self.cI = IncrementalSolver()
            self.sets = []

    def add(self, elem):
        self.sets.append(elem)
        I = self.I
        cI = self.cI
        expr = elem.as_expr()
        if cI.is_sat(expr):
            assert I is None or not intersection(complement(I), elem).is_empty()
            # the elem is not a subset of current set
            if I:
                I.add(elem)
                I.reset_expr(I.as_expr().rewrite_and_simplify())
            else:
                self.I = elem
            cI.add(complement(elem).as_expr())

    def includes(self, elem):
        # intersection(complement(self.I), elem).is_empty()
        return self.cI.is_sat(elem.as_expr()) is False

    def __repr__(self):
        return self.I.__repr__()


class KindSEChecker(BaseKindSE):
    """
    An executor that recursively checks the validity of one particular assertion.
    It inherits from BaseKindSE to have the capabilities to execute paths.
    """

    def __init__(self, toplevel_executor, loc, A, invariants=None):
        super().__init__(
            toplevel_executor.getProgram(),
            ohandler=None,
            opts=toplevel_executor.getOptions(),
            programstructure=toplevel_executor.programstructure,
        )
        self.location = loc
        self.assertion = A
        self.toplevel_executor = toplevel_executor
        self.create_set = self.ind_executor().create_states_set
        self.get_loop = toplevel_executor.programstructure.get_loop

        # paths to still search
        self.readypaths = []
        # inductive sets that we generated
        self.invariant_sets = {} if invariants is None else invariants
        # inductive sets for deriving starting sequences
        self.inductive_sets = {}

        if __debug__ and invariants:
            dbg("Have these invariants at hand:")
            for loc, invs in invariants.items():
                dbg(f"  @ {loc}: {invs}")

        self.no_sum_loops = set()

    def executePath(self, path, fromInit=False):
        """
        Override executePath such that it uses invariants that we have
        """
        return super().executePath(
            path, fromInit=fromInit, invariants=self.invariant_sets
        )

    def unfinished_paths(self):
        return self.readypaths

    def check_loop_precondition(self, L, A):
        loc = L.header()
        dbg_sec(f"Checking if {A} holds on {loc}")

        # def reportfn(msg, *args, **kwargs):
        #     print_stdout(f"> {msg}", *args, **kwargs)

        # run recursively KindSEChecker with already computed inductive sets
        checker = KindSEChecker(
            self.toplevel_executor,
            loc,
            A,
            invariants=self.invariant_sets
        )
        result, states = checker.check(L.entries())
        dbg_sec()
        return result, states

    def unwind(self, paths, maxk):
        assert maxk
        k = 0
        dbg("Unwinding the loop...")
        while paths and k < maxk:
            newpaths = []
            for p in paths:
                r, states = self.check_path(p)
                if r is Result.UNSAFE:
                    # we hit real unsafe path - return it so that the main executor
                    # will re-execute it and report
                    return Result.UNSAFE, [p]
                # otherwise just prolong the paths that failed
                if states.errors:
                     newpaths.extend(self.extend_paths(p, None))
            paths = newpaths
            k += 1
        return Result.UNKNOWN if paths else Result.SAFE, paths

    def handle_loop(self, loc, path, states):
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

        # check subsumption by inductive sets
        unsafe = states.errors
        assert unsafe, "No unsafe states, we should not get here at all"

        #   # first try to unroll it in the case the loop is easy to verify
        #   kindse = BaseKindSE(self.getProgram())
        maxk = 15
        dbg_sec("Running nested KindSE")
        res, unwoundloop = self.unwind([path.copy()], maxk=maxk)
        dbg_sec()
        if res is Result.SAFE:
           print_stdout(
               f"Loop {loc} proved by unwinding", color="GREEN"
           )
           return res, []
        elif res is Result.UNSAFE:
           self.no_sum_loops.add(loc)
           return res, [path]  # found an error

        L = self.get_loop(loc)
        if L is None:
            print_stdout("Was not able to construct the loop info")
            print_stdout(f"Falling back to unwinding loop {loc}", color="BROWN")
            self.no_sum_loops.add(loc)
            return Result.UNKNOWN, unwoundloop

        if self.fold_loop(path, loc, L, unsafe):
            return Result.SAFE, []
        else:
            # NOTE: do not return unwoundloop, we must not return more
            # than one iteration to preserve the initial sets inductive
            return Result.UNKNOWN, self.extend_paths(path, None)

    def extend_seq(self, seq, target0, E, L):
        """
        Compute the precondition for reaching S and overapproximate it

        S - target states
        E - error states
        """
        target = self.create_set(seq[-1].toassert()) if seq else target0
        r = check_paths(self, L.paths(), post=target)
        if not r.ready:  # cannot step into this frame...
            # FIXME we can use it at least for annotations
            dbg("Infeasible frame...")
            return
        for s in r.killed():
            dbg("Killed a state")
            self.report(s)
            return

        for s in r.ready:
            if not intersection(E, s).is_empty():
                dbg("Pre-image is not safe...")
                # FIXME: should we do the intersection with complement of E?
                continue
            A = overapprox(self, s, E, target, L)
            if A is None:
                dbg("Overapproximation failed...")
                continue

            if __debug__:
                assert (
                    seq is None or intersection(A, E).is_empty()
                ), f"Overapproximation is not safe: {A}"
            # FIXME: intersect with all inductive sets?
            if seq and intersection(A, complement(target)).is_empty():
                dbg("Did not extend (got included elem...)")
                continue

            yield A

   #def abstract_seq(self, seq, errs0, L):
   #    # don't try with short sequences
   #    if len(seq) < 5:
   #        return seq

   #    # try to merge last two frames
   #    assert len(seq) >= 2
   #    A1 = seq[-1].toassume()
   #    A2 = seq[-2].toassume()
   #    e1 = A1.expr().to_cnf()
   #    e2 = A2.expr().to_cnf()

   #    C1 = set(e1.children())
   #    C = set()
   #    N1 = set()
   #    N2 = set()
   #    for c in e2.children():
   #        if c in C1:
   #            C.add(c)
   #        else:
   #            N2.add(c)
   #    for c in C1:
   #        if c not in C:
   #            N1.add(c)

   #    if not C:
   #        return seq

   #    # replace last two frames with one merged frame
   #    EM = getGlobalExprManager()
   #    seq.pop()

   #    seq[-1].states = AssertAnnotation(EM.conjunction(*C), A1.substitutions(), EM)
   #    S1 = AssertAnnotation(EM.conjunction(*N1), A1.substitutions(), EM)
   #    S2 = AssertAnnotation(EM.conjunction(*N2), A2.substitutions(), EM)
   #    seq[-1].strengthening = or_annotations(EM, True, S1, S2)

   #    # FIXME: we are still precise, use abstraction here...
   #    return seq

    def initial_seq_from_last_iter(self, E: StatesSet, L: Loop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """

        create_set = self.create_set
        is_error_loc = L.cfa().is_err
        # get the safe states that jump out of the loop after one iteration - for safety
        # (these will include conditions from passed assertions)
        r = check_paths(
            self,
            (p for p in L.last_iteration_paths() if not is_error_loc(p.last_loc())),
        )
        ready = r.ready
        assert ready, "Loop has only infeasible paths"
        for s in r.killed():
            dbg("Killed a state")
            self.report(s)
            return None
        R = create_set()
        rempty = True

        # FIXME: we can use only a subset of the states, wouldn't that be better?

        for r in ready:
            tmp = R.copy()
            tmp.add(r)
            tmpseq = InductiveSequence(tmp.as_assert_annotation())
            # failure may mean that the assertion in fact does not hold
            if is_seq_inductive(tmpseq, None, self, L):
                rempty = False
                R.add(r)

        if rempty:
            r = check_paths(
                self,
                (p for p in L.get_exit_paths() if not is_error_loc(p[-1].target())),
            )
            if r.ready is None:
                return None

            I = create_set()
            I.add(r.ready)
            assert is_seq_inductive(InductiveSequence(I.as_assert_annotation()), None, self, L)
            R.add(I)
            assert is_seq_inductive(InductiveSequence(R.as_assert_annotation()), None, self, L)

        if not intersection(R, E).is_empty():
            dbg("... (intersection with unsafe states is non-empty)")
            dbg("   trying to fix it")
            R.intersect(complement(E))
            if R.is_empty():
                return None

        seq0 = InductiveSequence(R.as_assert_annotation())
        # this may mean that the assertion in fact does not hold
        if is_seq_inductive(seq0, None, self, L):
            return seq0
        dbg("... (got non-inductive set)")
        return None


    def get_initial_seq(self, unsafe : list, path : AnnotatedCFAPath, L : Loop):
        assert len(unsafe) == 1, "One path raises multiple unsafe states"

        # TODO: self-loops? Those are probably OK as that would be only assume edge
        errstate = unsafe[0]
        EM = errstate.expr_manager()
        isfirst = path.num_of_occurences(L.header()) == 1
        E = self.create_set(errstate)

        S = E.copy()
        C = errstate.getConstraints()
        S.reset_expr(EM.conjunction(*C[:-1], EM.Not(C[-1])))
        target0 = S.copy()

        if isfirst:
            # last constraint is the failed assertion
            # first constraint is the loop exit condition
            S.intersect(unsafe[0].getConstraints()[0])
            # if the assertion is after the loop, the set is now inductive

        seq0 = InductiveSequence(S.as_assert_annotation(), None)
        errs0 = InductiveSequence.Frame(E.as_assert_annotation(), None)

        if not is_seq_inductive(seq0, None, self, L):
            # the initial sequence may not be inductive (usually when the assertion
            # is inside the loop, so we must strenghten it in that case
            if isfirst:
                # FIXME: return sets
                seq0 = self.initial_seq_from_last_iter(E, L)
                assert seq0 and is_seq_inductive(seq0, None, self, L),\
                       "Failed getting init seq for first iteration"
            else:
                seq0 = self.strengthen_initial_seq(seq0, E, path, L)

        assert seq0 is None or is_seq_inductive(seq0, None, self, L)

        # reduce and over-approximate the initial sequence
        if seq0:
            seq0 = self.overapprox_init_seq(seq0, errs0, L)

        # inductive sequence is either inductive now, or it is None and we'll use non-inductive E
        return target0, seq0, errs0

    def overapprox_init_seq(self, seq0, errs0, L):
        assert is_seq_inductive(seq0, None, self, L), "seq is not inductive"

        create_set = self.create_set
        target = create_set(seq0[-1].toassert())
        S = create_set(seq0.toannotation(True))
        if S.is_empty():
            dbg("Starting sequence is empty")
            return None
        S.reset_expr(S.as_expr().rewrite_and_simplify())
        assert not S.is_empty(), f"Starting sequence is infeasible!: {seq0}"
        EM = getGlobalExprManager()
        seq = InductiveSequence(
            overapprox_set(
                self, EM, S, errs0.toassert(), target, L
            ).as_assert_annotation()
        )
        if is_seq_inductive(seq, None, self, L):
            return seq
        dbg("Overapproximated starting sequence is not inductive")
        return seq0

    def safe_path_with_last_iter(self, E, path, L: Loop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """

        is_error_loc = L.cfa().is_err

        prefix = strip_last_assume_edge(path)
        middle = L.paths_to_header(prefix.last_loc())
        suffix = [p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())]

        invpaths = (AnnotatedCFAPath(prefix.edges() + m.edges() + s.edges()) for m in middle for s in suffix)

        create_set = self.create_set
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        r = check_paths(self, chain(invpaths, iter(suffix)))
        if r.ready is None:
            return None

        I = create_set()
        I.add(r.ready)
        if not intersection(I, E).is_empty():
            dbg("... (intersection with unsafe states is non-empty)")
            dbg("   trying to fix it")
            I.intersect(complement(E))
            if I.is_empty():
                return None

        return I

    def strengthen_initial_seq(self, seq0, E, path, L: Loop):
        assert path[0].source() is L.header()
        assert len(seq0) == 1

        create_set = self.create_set
        # FIXME: do we need this check?
        if create_set(seq0.toannotation(True)).is_empty():
            dbg("Initial sequence is empty", color="wine")
            return None

        S = create_set(seq0.toannotation())
        S.reset_expr(S.as_expr().rewrite_and_simplify())
        dbg("Initial sequence is NOT inductive, fixing it", color="wine")

        # get the inductive sets that we have created for this header.
        # Since we go iteration over iteration, adding this sequence
        # to the previous ones must yield an inductive sequence
        IS = self.inductive_sets.get(L.header())
        assert IS, "No inductive sequence for non-first iteration"

        if not intersection(IS.I, E).is_empty():
            dbg("The inductive sets are not disjunctive with error states")
            return None

        frame = seq0[-1].toassert()
        # first check whether the frame is included in our inductive sequences.
        # If so, we'll just add relations from it to the sequences
        # (for boosing over-approximations) instead of adding it whole.
        frameset = create_set(frame)
        if IS.includes(frameset):
            dbg("States are included, continuing with previous sequences")
            F = IS.I.copy()
        else:
            F = union(IS.I, frame)
        tmp = InductiveSequence(union(F).as_assert_annotation())
        # FIXME: simplify as much as you can before using it
        if is_seq_inductive(tmp, None, self, L):
            return tmp
        # this must be assertion inside the loop -- we must simulate that the path
        # passes the assertion and jumps out of the loop
        I = self.safe_path_with_last_iter(E, path, L)
        if I is None:
            return None

        tmp = InductiveSequence(union(I, frame).as_assert_annotation())
        # FIXME: simplify as much as you can before using
        if is_seq_inductive(tmp, None, self, L):
            return tmp

        dbg("-- Failed making the initial sequence inductive --", color="red")
        return None

    def fold_loop(self, path, loc, L: Loop, unsafe):
        dbg(f"========== Folding loop {loc} ===========")
        if __debug__:
            _dump_inductive_sets(self, loc)

        assert unsafe, "No unsafe states, we should not get here at all"
        create_set = self.create_set

        dbg(f"Getting initial sequence for loop {loc}")
        target0, seq0, errs0 = self.get_initial_seq(unsafe, path, L)
        if seq0 is None:
            print_stdout(
                f"Failed getting initial inductive sequence for loop {loc}", color="red"
            )
            # FIXME: the initial element must be inductive, otherwise we do not know whether
            # an error state is unreachable from it...

            # store the non-inductive sequence -- in the future,
            # these states may be necessary when doing the set
            # inductive
            newi = create_set(target0.as_assert_annotation())
            I = self.inductive_sets.setdefault(loc, InductiveSet())
            I.add(newi)

            return False
        assert seq0

        if __debug__:
            assert (
                seq0 is None
                or intersection(
                    create_set(seq0.toannotation()), errs0.toassert()
                ).is_empty()
            ), "Initial sequence contains error states"

        sequences = [seq0]
        E = create_set(errs0.toassert())

        print_stdout(f"Executing loop {loc} with assumption", color="white")
        print_stdout(str(seq0[0]) if seq0 else str(target0), color="white")
        print_stdout(f"and errors : {errs0}")

        max_seq_len = 2*len(L.paths())
        while True:
            print_stdout(
                f"Got {len(sequences)} abstract path(s) of loop " f"{loc}",
                color="GRAY",
            )
            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for seq in sequences:
                if seq:
                    S = seq.toannotation(True)
                    res, _ = self.check_loop_precondition(L, S)

                    newi = create_set(seq[-1].toassume())
                    I = self.inductive_sets.setdefault(loc, InductiveSet())
                    I.add(newi)

                    if res is Result.SAFE:
                        invs = self.invariant_sets.setdefault(loc, [])
                        inv = seq.toannotation(False)
                        invs.append(inv)
                        # FIXME: check that the invariant gives us a new information
                        # I = create_set() # FIXME: cache the union of invariants
                        # I.add(invs)
                        # I.intersect()
                        print_stdout(f"{S} holds on {loc}", color="BLUE")
                        return True


            extended = []
            for seq in sequences:
                print_stdout(
                    f"Processing sequence of len {len(seq) if seq else 0}:\n{seq}",
                    color="dark_blue",
                )
                if __debug__:
                    assert (
                        seq is None
                        or intersection(
                            create_set(seq.toannotation(True)), errs0.toassert()
                        ).is_empty()
                    ), "Sequence is not safe"
                    assert seq is None or is_seq_inductive(
                        seq, target0, self, L
                    ), "seq is not inductive"

                if seq and len(seq) >= max_seq_len:
                    dbg("Give up extending the sequence, it is too long")
                    continue

                dbg("Extending the sequence")
                # FIXME: we usually need seq[-1] as annotation, or not?
                for A in self.extend_seq(seq, target0, E, L):
                    print_stdout(f"Extended with: {A}", color="BROWN")
                    tmp = seq.copy() if seq else InductiveSequence()
                    tmp.append(A.as_assert_annotation(), None)
                    if __debug__:
                        r = tmp.check_ind_on_paths(self, L.paths(), target0)
                        assert (
                            r.errors is None
                        ), f"Extended sequence is not inductive (CTI: {r.errors[0].model()})"

                    # extended.append(self.abstract_seq(e, errs0, L))
                    extended.append(tmp)
                dbg("Extending the sequence finished")

            if not extended:
                dbg("Failed extending any sequence")
                # seq not extended... it looks that there is no
                # safe invariant
                # FIXME: could we use it for annotations?
                print_stdout("Failed extending any sequence", color="orange")
                return False  # fall-back to unwinding

            sequences = extended

    def check_path(self, path):
        first_loc = path[0]
        if self._is_init(first_loc.source()):
            r, states = self.checkInitialPath(path)
            if r is Result.UNSAFE:
                self.reportfn(f"Error path: {path}", color="red")
                return r, states  # found a real error
            elif r is Result.SAFE:
                # dbgv(f"Safe (init) path: {path}", color="dark_green")
                return None, states  # this path is safe
            elif r is Result.UNKNOWN:
                for s in states.killed():
                    self.report(s, self.reportfn)
                # dbgv(f"Inconclusive (init) path: {path}")
                self.problematic_paths.append(path)
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
        # problem = False
        for s in chain(killed1, killed2):
            # problem = True
            self.report(s, fn=self.reportfn)
            self.reportfn(f"Killed states when executing {path}")
            self.problematic_paths.append(path)

        # if r.errors:
        #    self.reportfn(f"Possibly error path: {path}", color="ORANGE")
        # elif problem:
        #    self.reportfn(f"Problem path: {path}", color="PURPLE")
        # else:
        #    self.reportfn(f"Safe path: {path}", color="DARK_GREEN")

        return None, r

    def get_path_to_run(self):
        ready = self.readypaths
        if ready:
            return heappop(ready)
        return None

    def is_loop_header(self, loc):
        return loc in self.programstructure.get_loop_headers()

    def queue_paths(self, paths):
        assert isinstance(paths, list), paths
        readyp = self.readypaths
        for p in paths:
            heappush(readyp, p)

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

        while True:
            path = self.get_path_to_run()
            if path is None:
                return (
                    Result.UNKNOWN if (self.problematic_paths) else Result.SAFE
                ), self.problematic_paths_as_result()

            ldbgv("Main loop: check path {0}", (path,))
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
                dbgv(f"Safe path: {path}")

        raise RuntimeError("Unreachable")


class KindSymbolicExecutor(BaseKindSE):
    """
    The main class for KindSE that divides and conquers the tasks.
    It inherits from BaseKindSE to have program structure and such,
    TODO but we should change that, build program structure here,
    and keep BaseKindSE a class that just takes care for executing paths.
    """

    def __init__(self, prog, ohandler=None, opts=KindSeOptions()):
        super().__init__(prog=prog, ohandler=ohandler, opts=opts)
        # Use invariants generated by one checker in other checkers
        self.propagate_invariants = True

        self.invariants = {}

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
            checker = KindSEChecker(self, loc, A, invariants=self.invariants)
            result, states = checker.check()
            if result is Result.UNSAFE:
                assert states.errors, "No errors in unsafe result"
                for s in states.errors:
                    self.report(s)
                print_stdout("Error found.", color="redul")
                return result
            elif result is Result.SAFE:
                print_stdout(
                    f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                )
            elif result is Result.UNKNOWN:
                print_stdout(f"Checking {A} at {loc} was unsuccessful.", color="yellow")
                has_unknown = True
                assert checker.problematic_paths, "Unknown with no problematic paths?"
                for p in checker.problematic_paths:
                    self.stats.killed_paths += 1
                    print_stdout(f"Killed path: {p}")

        if has_unknown:
            print_stdout("Failed deciding the result.", color="orangeul")
            return Result.UNKNOWN

        print_stdout("No error found.", color="greenul")
        return Result.SAFE
