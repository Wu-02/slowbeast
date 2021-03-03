from heapq import heappush, heappop
from itertools import chain
from slowbeast.util.debugging import print_stderr, print_stdout, dbg, dbg_sec, dbgv, ldbgv

from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.kindse.naive.naivekindse import Result
from slowbeast.kindse import KindSEOptions
from slowbeast.symexe.statesset import intersection, union, complement, StatesSet
from slowbeast.symexe.symbolicexecution import SEStats
from slowbeast.analysis.loops import Loop
from slowbeast.kindse.kindse.programstructure import ProgramStructure

from slowbeast.symexe.annotations import (
    AssertAnnotation,
    state_to_annotation
)

from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver

from .kindsebase import check_paths, KindSymbolicExecutor as BaseKindSE
from .inductivesequence import InductiveSequence
from .overapproximations import overapprox_set

class BSELFOptions(KindSEOptions):
    def __init__(self, copyopts=None):
        super().__init__(copyopts)
        if copyopts:
            self.fold_loops = copyopts.fold_loops = True
            self.simple_sis = copyopts.simple_sis = False
            self.target_is_whole_seq = copyopts.target_is_whole_seq = True
        else:
            self.fold_loops = True
            self.simple_sis = False
            self.target_is_whole_seq = True

    def default(self, parentopts=None):
        n = BSELFOptions()
        if parentopts:
            super(self).__init__(parentopts)

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
    if S.is_empty():
        dbg("Starting sequence is empty")
        return None

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
    return overapprox_set(executor, s.expr_manager(), S, E, target, L)

def report_state(stats, n, fn=print_stderr):
    if n.hasError():
        if fn:
            fn(
                "state {0}: {1}, {2}".format(n.get_id(), n.pc, n.getError()),
                color="RED",
            )
        stats.errors += 1
    elif n.wasKilled():
        if fn:
            fn(n.getStatusDetail(), prefix="KILLED STATE: ", color="WINE")
        stats.killed_paths += 1


def is_seq_inductive(seq, target, executor, L, has_ready=False):
    r = seq.check_ind_on_paths(executor, L.paths(), target)
    for s in r.killed():
        dbg("Killed a state")
        report_state(executor.stats, s)
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

def strip_last_exit_edge(path: AnnotatedCFAPath, exits):
    idx = path.last_edge_of_idx(exits)
    # we use this func only on loop edges, so it must contain the entry condition
    assert idx is not None and idx + 1 < len(path), idx
    return path.subpath(0, idx - 1)


def suffixes_starting_with(paths, loc):
    for path in paths:
        for idx in range(len(path)):
            if path[idx].source() == loc:
                yield path.subpath(idx)

# def can_reach_header(loc, header, headers):
#     " headers - other loop headers, we stop there"
#
#     hit_headers = set()
#     def processedge(edge, dfstype):
#         t = edge.target()
#         if t in headers:
#             hit_headers.add(t)
#
#     DFSVisitor(stop_vertices=headers).foreachedge(loc, processedge)
#     return header in hit_headers


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
            else:
                self.I = elem
            cI.add(complement(elem).as_expr())

    def includes(self, elem):
        if isinstance(elem, InductiveSet):
            elem = elem.I
        # intersection(complement(self.I), elem).is_empty()
        return self.cI.is_sat(elem.as_expr()) is False

    def __repr__(self):
        return self.I.__repr__()


class BSELFChecker(BaseKindSE):
    """
    An executor that recursively checks the validity of one particular assertion.
    It inherits from BaseKindSE to have the capabilities to execute paths.
    """

    def __init__(self, loc, A, program, programstructure, opts,
                 invariants=None, indsets=None):
        super().__init__(
            program,
            ohandler=None,
            opts=opts,
            programstructure=programstructure,
        )
        assert isinstance(opts, BSELFOptions), opts
        self.program = program
        self.location = loc
        self.assertion = A

        self.options = opts
        self._target_is_whole_seq = opts.target_is_whole_seq
        self._simple_sis = opts.simple_sis

        self.create_set = self.ind_executor().create_states_set
        self.get_loop = programstructure.get_loop
        self.get_loop_headers= programstructure.get_loop_headers


        # paths to still search
        self.readypaths = []
        # inductive sets that we generated
        self.invariant_sets = {} if invariants is None else invariants
        # inductive sets for deriving starting sequences
        self.inductive_sets = indsets or {}

        if __debug__ and invariants:
            dbg("Have these invariants at hand:")
            for loc, invs in invariants.items():
                dbg(f"  @ {loc}: {invs}")

        self.no_sum_loops = set()

    def execute_path(self, path, fromInit=False):
        """
        Override execute_path such that it uses invariants that we have
        """
        return super().execute_path(
            path, fromInit=fromInit, invariants=self.invariant_sets
        )

    def unfinished_paths(self):
        return self.readypaths

    def check_loop_precondition(self, L, A):
        loc = L.header()
        dbg_sec(f"Checking if {A} holds on {loc}")

        # def reportfn(msg, *args, **kwargs):
        #     print_stdout(f"> {msg}", *args, **kwargs)

        # run recursively BSELFChecker with already computed inductive sets
        checker = BSELFChecker(
            loc,
            A,
            self.program,
            self.programstructure,
            self.options,
            indsets=self.inductive_sets,
            invariants=self.invariant_sets,
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
        dbg_sec(f"Unwinding the loop {maxk} steps")
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
        if self._target_is_whole_seq:
            target = self.create_set(seq[-1].toassert()) if seq else target0
        else:
            target = self.create_set(seq.toannotation(True)) if seq else target0
        r = check_paths(self, L.paths(), post=target)
        if not r.ready:  # cannot step into this frame...
            dbg("Infeasible frame...")
            # FIXME: remove this sequence from INV sets
            return
        for s in r.killed():
            dbg("Killed a state")
            report_state(self.stats, s)
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

    def initial_seq_from_last_iter(self, E: StatesSet, path, L: Loop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """

        dbg("Obtaining states from last safe iterations")
        I = self.safe_path_with_last_iter(E, path, L)
        if I is None:
            return None

        seq0 = InductiveSequence(I.as_assert_annotation())
        # this may mean that the assertion in fact does not hold
        if is_seq_inductive(seq0, None, self, L):
            return seq0
        dbg("... (got non-inductive set)")
        return None

    def get_simple_initial_seqs(self, unsafe : list, path : AnnotatedCFAPath, L : Loop):
        E = self.create_set(unsafe[0])

        S = E.copy()
        S.complement()
        target0 = S.copy()

        seq0 = InductiveSequence(S.as_assert_annotation(), None)
        if not is_seq_inductive(seq0, None, self, L):
            dbg("... (complement not inductive)")
            seqs = []
            Is = self.initial_sets_from_is(E, L)
            if not Is:
                dbg("... (no match in inductive sets)")
                Is = self.initial_sets_from_exits(E, path, L)
            if Is:
                for s in (InductiveSequence(I.as_assert_annotation(), None) for I in Is):
                    dbg("... (got first IS)")
                    # should be inductive from construction
                    assert is_seq_inductive(s, None, self, L), 'seq is not inductive'
                    seqs.append(s)
                   #if is_seq_inductive(s, None, self, L):
                   #    seqs.append(s)
            seqs = seqs or None
        else:
            dbg("... (complement is inductive)")
            seqs = [seq0]

        errs0 = InductiveSequence.Frame(E.as_assert_annotation(), None)
        return target0, seqs, errs0


    def get_acc_initial_seqs(self, unsafe : list, path : AnnotatedCFAPath, L : Loop):
        # TODO: self-loops? Those are probably OK as that would be only assume edge
        errstate = unsafe[0]
        EM = errstate.expr_manager()
        isfirst = path.num_of_occurences(L.header()) == 1
        E = self.create_set(errstate)

        S = E.copy()
        C = errstate.getConstraints()
        S.reset_expr(EM.conjunction(*C[:-1], EM.Not(C[-1])))
        target0 = S.copy()

        seq0 = InductiveSequence(S.as_assert_annotation(), None)
        seqs = [seq0]

        if not is_seq_inductive(seq0, None, self, L):
            # the initial sequence may not be inductive (usually when the assertion
            # is inside the loop, so we must strenghten it in that case
            if isfirst:
                # FIXME: return sets
                dbg("Getting the initial sequence from the last iteration")
                seq0 = self.initial_seq_from_last_iter(E, path, L)
                assert seq0 and is_seq_inductive(seq0, None, self, L),\
                       "Failed getting init seq for first iteration"
                seqs = [seq0] if seq0 else None
            else:
                dbg("Initial sequence is NOT inductive, fixing it", color="wine")
                seqs = self.strengthen_initial_seq(seq0, E, path, L)

        errs0 = InductiveSequence.Frame(E.as_assert_annotation(), None)
        return target0, seqs, errs0

    def get_initial_seqs(self, unsafe : list, path : AnnotatedCFAPath, L : Loop):
        assert len(unsafe) == 1, "One path raises multiple unsafe states"

        if self._simple_sis:
            target0, seqs, errs0 = self.get_simple_initial_seqs(unsafe, path, L)
        else:
            target0, seqs, errs0 = self.get_acc_initial_seqs(unsafe, path, L)
        # reduce and over-approximate the initial sequence
        if seqs:
            seqs = [self.overapprox_init_seq(seq, errs0, L) for seq in seqs]

        # inductive sequence is either inductive now, or it is None and we'll use non-inductive E
        return target0, seqs, errs0

    def overapprox_init_seq(self, seq0, errs0, L):
        assert is_seq_inductive(seq0, None, self, L), "seq is not inductive"

        create_set = self.create_set
        target = create_set(seq0[-1].toassert())
        S = create_set(seq0.toannotation(True))
        #assert not S.is_empty(), f"Starting sequence is infeasible!: {seq0}"
        if S.is_empty():
            return None
        EM = getGlobalExprManager()
        seq = InductiveSequence(
            overapprox_set(
                self, EM, S, errs0.toassert(), target, L
            ).as_assert_annotation()
        )

        if is_seq_inductive(seq, None, self, L):
            return seq
        return seq0

    def _safe_paths_err_outside(self, E, path, L):
        EM = getGlobalExprManager()
        create_set = self.create_set
        added = False
        I = create_set()

        for suffix in suffixes_starting_with([path], L.header()):
            # execute the safe path that avoids error and then jumps out of the loop
            # and also only paths that jump out of the loop, so that the set is inductive
            r = check_paths(self, [suffix])
            if r.errors is None:
                continue

            for e in r.errors:
                C = e.getConstraints()
                # negate the last constraint on the path
                tmp = create_set(e)
                expr = EM.conjunction(*C[:-1], EM.Not(C[-1]))
                tmp.reset_expr(expr)

                if intersection(E, tmp).is_empty():
                    I.add(tmp)
                    added = True

        if added:
            return I

        return None

    def _safe_paths_err_inside(self, E, path, L):
        create_set = self.create_set
        is_error_loc = L.cfa().is_err
        added = False
        I = create_set()

        prefix = strip_last_exit_edge(path, L.exits())
        middle = L.paths_to_header(prefix.last_loc())
        suff = [p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())]

        paths = (AnnotatedCFAPath(prefix.edges() + m.edges() + s.edges()) for m in middle for s in suff)

        for suffix in suffixes_starting_with(paths, L.header()):
            # execute the safe path that avoids error and then jumps out of the loop
            # and also only paths that jump out of the loop, so that the set is inductive
            r = check_paths(self, [suffix])
            if not r.ready:
                continue
            for s in r.ready:
                if intersection(create_set(s), E).is_empty():
                    I.add(s)
                    added = True

        if added:
            return I

        return None


    def safe_paths_from_iterations(self, E, path, L):
        # FIXME: do a proper analysis of whether the error loc is inside or outside the loop
        # instead of trying blindly
        I = self._safe_paths_err_outside(E, path, L)
        if I and is_seq_inductive(InductiveSequence(I.as_assert_annotation(), None), None, self, L):
            return I

        I = self._safe_paths_err_inside(E, path, L)
        if I and is_seq_inductive(InductiveSequence(I.as_assert_annotation(), None), None, self, L):
            return I
        return None

    def safe_path_with_last_iter(self, E, path, L: Loop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """

        is_error_loc = L.cfa().is_err

        prefix = strip_last_exit_edge(path, L.exits())
        middle = L.paths_to_header(prefix.last_loc())
        suff = [p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())]

        invpaths = (AnnotatedCFAPath(prefix.edges() + m.edges() + s.edges()) for m in middle for s in suff)

        create_set = self.create_set
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        r = check_paths(self, chain(invpaths, iter(suff)))
        if r.ready is None:
            return None

        I = create_set()
        added = False
        for s in r.ready:
            if intersection(create_set(s), E).is_empty():
                I.add(s)
                added = True

        if added:
            return I

        return None

    def initial_sets_from_exits(self, E, path, L: Loop):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.

        FIXME: we actually do not use the assertion at all right now,
        only implicitly as it is contained in the paths...
        """

        is_error_loc = L.cfa().is_err
        create_set = self.create_set
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        cE = complement(E)
        sets = []
        for p in (p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())):
            r = check_paths(self, [p])
            assert r.ready is not None, "Infeasible exit paths from loop"

            tmp = create_set()
            tmp.add(r.ready)
            tmp.intersect(cE)
            sets.append(tmp)
        return sets

    def initial_sets_from_is(self, E, L):
        # get the inductive sets that we have created for this header.
        # Since we go iteration over iteration, adding this sequence
        # to the previous ones must yield an inductive sequence
        isets = self.inductive_sets.get(L.header())
        if isets is None:
            return None
        R = self.create_set()
        added = False

        dbg("Checking inductive sets")
        for I in isets:
            if intersection(I.I, E).is_empty():
                R.add(I.I)
                added = True
        if added:
            return [R]
        return None


    def strengthen_initial_seq(self, seq0, E, path, L: Loop):
        assert path[0].source() is L.header()
        assert len(seq0) == 1

        # get the inductive sets that we have created for this header.
        # Since we go iteration over iteration, adding this sequence
        # to the previous ones must yield an inductive sequence
        isets = self.inductive_sets.get(L.header())
        assert isets, "No inductive sequence for non-first iteration"

        dbg("Checking inductive sets")
        ret = []
        for I in isets or ():
            if intersection(I.I, E).is_empty():
                frame = seq0[-1].toassert()
                # first check whether the frame is included in our inductive sequences.
                # If so, we'll just add relations from it to the sequences
                # (for boosing over-approximations) instead of adding it whole.
                frameset = self.create_set(frame)
                if I.includes(frameset):
                    dbg("States are included, continuing with previous sequences")
                    F = I.I.copy()
                else:
                    dbg("States not included in previous sequences, trying to extend it")
                    F = union(I.I, frame)
                tmp = InductiveSequence(F.as_assert_annotation())
                # FIXME: simplify as much as you can before using it
                if is_seq_inductive(tmp, None, self, L):
                    #dbg("Joining with previous sequences did the trick")
                    print_stdout("Succeeded joining with a previous sequence")
                    ret.append(tmp)
                    break
            else:
                dbg("Inductive sequence is unsafe")
        if ret:
            return ret

        print_stdout("Creating new inductive sequence")
        # this must be assertion inside the loop -- we must simulate that the path
        # passes the assertion and jumps out of the loop
        I = self.safe_paths_from_iterations(E, path, L)
        if I is None:
            return None

        tmp = InductiveSequence(I.as_assert_annotation())
        # FIXME: simplify as much as you can before using
        if is_seq_inductive(tmp, None, self, L):
            return [tmp]
        dbg("Failed strengthening the initial sequence")
        return None

    def fold_loop(self, path, loc, L: Loop, unsafe):
        dbg(f"========== Folding loop {loc} ===========")
        if __debug__:
            _dump_inductive_sets(self, loc)

        assert unsafe, "No unsafe states, we should not get here at all"
        create_set = self.create_set

        dbg(f"Getting initial sequence for loop {loc}")
        target0, seqs0, errs0 = self.get_initial_seqs(unsafe, path, L)
        if seqs0 is None:
            print_stdout(
                f"Failed getting initial inductive sequence for loop {loc}", color="red"
            )
            # FIXME: the initial element must be inductive, otherwise we do not know whether
            # an error state is unreachable from it...
            return False
        assert seqs0

       #if __debug__:
       #    assert (
       #        seq0 is None
       #        or intersection(
       #            create_set(seq0.toannotation()), errs0.toassert()
       #        ).is_empty()
       #    ), "Initial sequence contains error states"

        sequences = seqs0
        E = create_set(errs0.toassert())

        print_stdout(f"Folding loop {loc} with errors {errs0}", color="white")

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

                    I = InductiveSet(create_set(S))
                    seqs = self.inductive_sets.setdefault(loc, [])
                    seqsid = id(seqs)
                    oldseqs = seqs.copy()
                    seqs.clear()
                    for olds in oldseqs:
                        if not I.includes(olds):
                            seqs.append(olds)
                    assert seqsid == id(seqs)
                    seqs.append(I)

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
                new_frames_complements = []
                for A in self.extend_seq(seq, target0, E, L):
                    drop = False
                    for C in new_frames_complements:
                        if intersection(C, A).is_empty():
                            print(f"Did not extended with: {A} (already has same or bigger frame)")
                            drop = True
                            break
                    if drop:
                        continue
                    new_frames_complements.append(complement(A))

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
            r, states = self.check_initial_error_path(path)
            if r is Result.UNSAFE:
                self.reportfn(f"Error path: {path}", color="red")
                return r, states  # found a real error
            elif r is Result.SAFE:
                # dbgv(f"Safe (init) path: {path}", color="dark_green")
                return None, states  # this path is safe
            elif r is Result.UNKNOWN:
                for s in states.killed():
                    report_state(self.stats, s, self.reportfn)
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

        r = self.execute_path(path)

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
            report_state(self.stats, s, fn=self.reportfn)
            self.reportfn(f"Killed states when executing {path}")
            self.problematic_paths.append(path)

        return None, r

    def get_path_to_run(self):
        ready = self.readypaths
        if ready:
            return heappop(ready)
        return None

    def is_loop_header(self, loc):
        return loc in self.get_loop_headers()

    def queue_paths(self, paths):
        assert isinstance(paths, list), paths
        readyp = self.readypaths
        for p in paths:
            heappush(readyp, p)

    def extend_paths(self, path, states):
        invpoints = self.get_loop_headers()
        return self.extend_path(
            path,
            states,
            steps=-1,
            atmost=True,
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

        opt_fold_loops = self.getOptions().fold_loops
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
                if opt_fold_loops:
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
                        continue
                self.extend_and_queue_paths(path, states)
            else:
                dbgv(f"Safe path: {path}")

        raise RuntimeError("Unreachable")


class BSELF:
    """
    The main class for KindSE that divides and conquers the tasks.
    It inherits from BaseKindSE to have program structure and such,
    TODO but we should change that, build program structure here,
    and keep BaseKindSE a class that just takes care for executing paths.
    """

    def __init__(self, prog, ohandler=None, opts=BSELFOptions()):
        assert isinstance(opts, BSELFOptions), opts
        self.program = prog
        self.ohandler = ohandler
        self.options = opts

        programstructure = ProgramStructure(prog, self.new_output_file)
        self.get_cfa = programstructure.cfas.get
        self.programstructure = programstructure

        self.stats = SEStats()

        self.invariants = {}


    # FIXME: make this a method of output handler or some function (get rid of 'self')
    # after all, we want such functionality with every analysis
    # FIXME: copied from BaseKindSE
    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

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
            checker = BSELFChecker(loc, A,
                                   self.program, self.programstructure, self.options,
                                   invariants=self.invariants)
            result, states = checker.check()
            self.stats.add(checker.stats)
            if result is Result.UNSAFE:
                assert states.errors, "No errors in unsafe result"
                for s in states.errors:
                    report_state(self.stats, s)
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
