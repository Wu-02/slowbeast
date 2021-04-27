from slowbeast.core.errors import AssertFailError
from slowbeast.util.debugging import (
    print_stdout,
    dbg,
    dbg_sec,
    ldbg,
    ldbgv,
    inc_print_indent,
    dec_print_indent,
)

from slowbeast.symexe.statesset import intersection, union, complement
from slowbeast.symexe.symbolicexecution import SEStats
from slowbeast.symexe.annotations import AssertAnnotation
from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.kindse.programstructure import ProgramStructure
from slowbeast.kindse.naive.naivekindse import Result
from slowbeast.kindse import KindSEOptions
from slowbeast.kindse.inductivesequence import InductiveSequence
from slowbeast.kindse.overapproximations import overapprox_set
from slowbeast.kindse.relations import get_const_cmp_relations, get_var_relations
from slowbeast.analysis.cfa import CFA
from slowbeast.solvers.solver import getGlobalExprManager

from .bse import (
    BackwardSymbolicInterpreter as BaseBSE,
    BSEContext,
    report_state,
    check_paths,
)
from .inductiveset import InductiveSet
from .loopinfo import LoopInfo


class BSELFOptions(KindSEOptions):
    def __init__(self, copyopts=None):
        super().__init__(copyopts)
        if copyopts:
            self.fold_loops = copyopts.fold_loops
            self.target_is_whole_seq = copyopts.target_is_whole_seq
            self.union_abstractions = copyopts.union_abstractions
            self.union_extensions = copyopts.union_extensions
            self.union_matched = copyopts.union_matched
            self.add_unwind_invariants = copyopts.add_unwind_invariants
        else:
            self.fold_loops = True
            self.target_is_whole_seq = True
            self.union_abstractions = False
            self.union_extensions_threshold = None
            self.union_matched = True
            self.add_unwind_invariants = False


def _dump_inductive_sets(checker, loc, fn=dbg):
    fn(f"With this INVARIANT set at loc {loc}:", color="dark_green")
    IS = checker.invariant_sets.get(loc)
    if IS:
        fn(f"\n{IS}", color="dark_green")
    else:
        fn(" ∅", color="dark_green")
    fn(f"With this INDUCTIVE set at loc {loc}:", color="dark_green")
    IS = checker.inductive_sets.get(loc)
    if IS:
        fn(f"\n{IS}", color="dark_green")
    else:
        fn(" ∅", color="dark_green")


def overapprox(executor, s, E, target, L):
    create_set = executor.create_set
    S = create_set(s)

    # FIXME: this is a workaround until we support nondet() calls in lazy execution
    r = check_paths(executor, L.paths(), pre=S, post=union(S, target))
    if r.errors:
        dbg(
            "FIXME: pre-image is not inductive cause we do not support nondets() in lazy execution yet"
        )
        return
    # --- workaround ends here...
    if S.is_empty():
        dbg("Starting sequence is empty")
        return

    # add relations
    for rel in get_const_cmp_relations(S.get_se_state()):
        ldbg("  Adding relation {0}", (rel,))
        # on_some, on_all = L.check_set_inductivity(create_set(rel))
        # if on_all:
        #    res, _ = executor.check_loop_precondition(L, rel)
        #    if res is Result.SAFE:
        #        # store the other sequences for further processing
        #        dbg("The relation is invariant!")
        #        # FIXME: check that we do not have this invariant already
        #        executor.add_invariant(L.header(), rel)
        #        continue

        S.intersect(rel)
        assert (
            not S.is_empty()
        ), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            S, E
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

    for rel in get_var_relations([S.get_se_state()], prevsafe=target):
        ldbg("  Using assumption {0}", (rel,))
        assumptions = create_set(rel)
        assert not intersection(
            assumptions, S
        ).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            assumptions, S, E
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

        assert not S.is_empty(), "Infeasible states given to overapproximate"
        yield overapprox_set(executor, s.expr_manager(), S, E, target, assumptions, L)

    # try without any relation
    assert not S.is_empty(), "Infeasible states given to overapproximate"
    yield overapprox_set(executor, s.expr_manager(), S, E, target, None, L)


def is_seq_inductive(seq, executor, L: LoopInfo):
    return L.set_is_inductive(executor.create_set(seq.toannotation()))


class BSELFChecker(BaseBSE):
    """
    An executor that recursively checks the validity of one particular assertion.
    In particular, it checks whether the given assertion holds when entering the
    given location.
    It inherits from BaseBSE to have the capabilities to execute paths.
    """

    def __init__(
        self,
        loc,
        A,
        program,
        programstructure,
        opts,
        invariants=None,
        indsets=None,
        max_loop_hits=None,
    ):
        super().__init__(
            program,
            ohandler=None,
            opts=opts,
            programstructure=programstructure,
            invariants=invariants,
        )
        assert isinstance(opts, BSELFOptions), opts
        self.program = program
        self.location = loc
        self.assertion = A

        self.options = opts
        self._target_is_whole_seq = opts.target_is_whole_seq

        self.create_set = self.ind_executor().create_states_set
        self.get_loop_headers = programstructure.get_loop_headers

        self.loop_info = {}

        # inductive sets for deriving starting sequences
        self.inductive_sets = indsets or {}

        if __debug__ and invariants:
            dbg("Have these invariants at hand:")
            for iloc, invs in invariants.items():
                dbg(f"  @ {iloc}: {invs}")

        self.no_sum_loops = set()
        self._loop_hits = {}
        self._max_loop_hits = max_loop_hits

    def get_loop(self, loc):
        L = self.loop_info.get(loc)
        if L is None:
            loop = self.programstructure.get_loop(loc)
            if loop is None:
                return None

            L = LoopInfo(self, loop)
            self.loop_info[loc] = L
        return L

    def check_loop_precondition(self, L, A):
        loc = L.header()
        print_stdout(f"Checking if {str(A)} holds on {loc}", color="purple")
        inc_print_indent()

        # run recursively BSELFChecker with already computed inductive sets
        checker = BSELFChecker(
            loc,
            A,
            self.program,
            self.programstructure,
            self.options,
            indsets=self.inductive_sets,
            invariants=self.invariant_sets,
            max_loop_hits=1,
        )
        result, states = checker.check(L.entries())

        dec_print_indent()
        dbg(f"Checking if {A} holds on {loc} finished")
        return result, states

    def execute_path(self, path, fromInit=False, invariants=None):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        if fromInit:
            # we must execute without lazy memory
            executor = self.executor()

            if not self.states:
                self.prepare()
            states = [s.copy() for s in self.states]
            assert states

            ldbgv("Executing (init) path: {0}", (path,), fn=self.reportfn)
        else:
            executor = self.ind_executor()

            s = executor.create_clean_state()
            states = [s]

            ldbgv("Executing path: {0}", (path,), fn=self.reportfn, color="orange")

        assert all(map(lambda s: not s.constraints(), states)), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.execute_annotated_path(states, path, invariants)
        self.stats.paths += 1

        earl = r.early
        if fromInit and earl:
            # this is an initial path, so every error is taken as real
            errs = r.errors or []
            for e in (e for e in earl if e.has_error()):
                errs.append(e)
            r.errors = errs

        return r

    def unwind_iteration(self, L, err):
        """
        Unroll the loop maxk times - that is, unroll the loop until you hit 'loc'
        in every feasible context maximally maxk times
        """
        queue = []
        for p in L.paths():
            queue.append(BSEContext(p, err.copy()))
        states = []
        for ctx in queue:
            pre = self._execute_path(ctx, invariants=self.invariant_sets)
            assert len(pre) <= 1, "Maximally one pre-states is supported atm"
            states.extend(pre)
        return states

    def unwind(self, loc, errpre, maxk=None):
        """
        Unroll the loop maxk times - that is, unroll the loop until you hit 'loc'
        in every feasible context maximally maxk times
        """
        queue = []
        for edge in loc.predecessors():
            queue.append(BSEContext(edge, errpre))

        if __debug__:
            k = 1
        while queue:
            if __debug__:
                ldbgv("Unwinding step {0}", (k,))
                k += 1
            newst = []
            for bsectx in queue:
                r, pre = self.precondition(bsectx)
                if r is Result.SAFE:
                    continue
                elif r is Result.UNSAFE:
                    return Result.UNSAFE

                if bsectx.path.source() == loc:
                    loc_hits = bsectx.loc_hits
                    lnm = loc_hits[loc] = loc_hits.get(loc, 0) + 1
                    if lnm > maxk:
                        # the loop is potentially unsafe on this path
                        # and we do not want to proceed further
                        return Result.UNKNOWN

                newst.append((pre, bsectx))

            queue = [
                bsectx.extension(pedge, pre.copy())
                for pre, bsectx in newst
                for pedge in bsectx.path[0].predecessors()
            ]

        # if queue is empty, we're safe!
        assert not queue, "Queue is not empty"
        return Result.SAFE

    def handle_loop(self, loc, errpre, loop_hit_no):
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

        assert errpre, "No unsafe states, we should not get here at all"
        unsafe = [errpre]

        # first try to unroll it in the case the loop is easy to verify
        maxk = 1  # unroll the loop only once
        dbg_sec(f"Unwinding the loop {maxk} steps")
        res = self.unwind(loc, errpre, maxk=maxk)
        dbg_sec()
        if res is Result.SAFE:
            if self.options.add_unwind_invariants:
                self.add_invariant(
                    loc, complement(self.create_set(errpre)).as_assume_annotation()
                )
            print_stdout(f"Loop {loc} proved by unwinding", color="GREEN")
            return True
        elif res is Result.UNSAFE:
            self.no_sum_loops.add(loc)
            return False

        L = self.get_loop(loc)
        if L is None:
            print_stdout("Was not able to construct the loop info")
            print_stdout(f"Falling back to unwinding loop {loc}", color="BROWN")
            self.no_sum_loops.add(loc)
            return False

        return self.fold_loop(loc, L, unsafe, loop_hit_no)

    def extend_seq(self, seq, E, L):
        new_frames_complements = []
        extended = []
        for A in self._extend_seq(seq, E, L):
            drop = False
            for C in new_frames_complements:
                if intersection(C, A).is_empty():
                    dbg(f"Did not extend with: {A} (already has same or bigger frame)")
                    drop = True
                    break
            if drop:
                continue
            new_frames_complements.append(complement(A))
            extended.append(A)
        if not extended:
            return
        union_threshold = self.options.union_extensions_threshold
        if union_threshold is not None and len(extended) >= union_threshold:
            dbg(f"Making union of extensions (threshold = {union_threshold})")
            yield union(*extended)
        else:
            for A in extended:
                yield A

    def _extend_seq(self, seq, E, L):
        """
        Compute the precondition for reaching S and overapproximate it

        S - target states
        E - error states
        """
        assert seq
        if self._target_is_whole_seq:
            target = self.create_set(seq[-1].toassert())
        else:
            target = self.create_set(seq.toannotation(True))
        r = check_paths(self, L.paths(), post=target)
        if not r.ready:  # cannot step into this frame...
            dbg("Infeasible frame...")
            # FIXME: remove this sequence from INV sets
            return
        for s in r.killed():
            dbg("Killed a state")
            report_state(self.stats, s)
            return

        toyield = []
        for s in r.ready:
            if not intersection(E, s).is_empty():
                dbg("Pre-image is not safe...")
                # FIXME: should we do the intersection with complement of E?
                continue
            for A in overapprox(self, s, E, target, L):
                if A is None:
                    dbg("Overapproximation failed...")
                    continue

                if __debug__:
                    assert (
                        seq is None or intersection(A, E).is_empty()
                    ), f"Overapproximation is not safe: {A}"

                # FIXME: intersect with all inductive sets?
                if target.contains(A):
                    dbg("Did not extend (got included elem...)")
                    continue

                ### keep only the overapproximations with the most models
                yield_seq = True
                # is A subsumed?
                for y in toyield:
                    if y.contains(A):
                        # seq is useless...
                        yield_seq = False
                        break
                if not yield_seq:
                    dbg("Subsumed an overapproximation...")
                    continue
                # filter out sets subsumed by A
                toyield = [y for y in toyield if not A.contains(y)]
                toyield.append(A)

            for A in toyield:
                yield A

    def get_initial_seqs(self, unsafe: list, L: LoopInfo, loop_hit_no: int):
        assert len(unsafe) == 1, "One path raises multiple unsafe states"
        E = self.create_set(unsafe[0])
        S = E.copy()
        S.complement()

        errs0 = InductiveSequence.Frame(E.as_assert_annotation(), None)
        seq0 = InductiveSequence(S.as_assert_annotation(), None)
        if S.is_empty():
            return None, errs0
        if not is_seq_inductive(seq0, self, L):
            dbg("... (complement not inductive)")
            seqs = []
            if loop_hit_no == 1:
                dbg("... (getting sis for the 1st hit of the loop)")
                Is = self.initial_sets_from_last_iters(E, L)
                assert Is, "Failed getting sequence for first visit"
                if not Is:
                    Is = self.initial_sets_from_is(E, L)
            else:
                dbg("... (joining with previously unfinished sequences)")
                Is = self.initial_sets_from_is(E, L)
                if Is is None:
                    Is = self.initial_sets_from_exits(E, L)
            if Is:
                for s in (
                    InductiveSequence(I.as_assert_annotation(), None) for I in Is
                ):
                    dbg("... (got first IS)")
                    # should be inductive from construction
                    assert is_seq_inductive(s, self, L), f"seq is not inductive: {s}"
                    seqs.append(s)
        else:
            dbg("... (complement is inductive)")
            seqs = [seq0]

        ### reduce and over-approximate the initial sequence
        # note: do that only on later than 1st iteration, because for the 1st iteration,
        # we already did that
        if seqs and loop_hit_no != 1:
            tmp = []
            print_stdout(
                f"Got {len(seqs)} starting inductive sequence(s)", color="dark_blue"
            )
            for seq in seqs:
                tmp.extend(self.overapprox_init_seq(seq, errs0, L))
            if tmp:
                seqs = tmp

        # inductive sequence is either inductive now, or it is None and we'll use non-inductive E
        return seqs or None, errs0

    def overapprox_init_seq(self, seq0, errs0, L):
        assert is_seq_inductive(seq0, self, L), "seq is not inductive"
        dbg("Overapproximating initial sequence")
        dbg(str(seq0))

        create_set = self.create_set
        target = create_set(seq0[-1].toassert())
        unsafe = create_set(errs0.toassert())
        S = create_set(seq0.toannotation(True))
        assert not S.is_empty(), f"Starting sequence is infeasible!: {seq0}"
        EM = getGlobalExprManager()

        # add relations
        for rel in get_const_cmp_relations(S.get_se_state()):
            ldbg("  Adding relation {0}", (rel,))
            S.intersect(rel)
            assert (
                not S.is_empty()
            ), f"Added realtion {rel} rendered the set infeasible\n{S}"
            assert intersection(
                S, unsafe
            ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

        yielded_seqs = []
        for rel in get_var_relations([S.get_se_state()], prevsafe=target):
            ldbg("  Using assumption {0}", (rel,))
            assumptions = create_set(rel)
            assert not intersection(
                assumptions, S
            ).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
            assert intersection(
                assumptions, S, unsafe
            ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

            seq = InductiveSequence(
                overapprox_set(
                    self, EM, S, errs0.toassert(), target, assumptions, L
                ).as_assert_annotation()
            )

            if is_seq_inductive(seq, self, L):
                # check if seq is a subset of some previously yielded sequence
                yield_seq = True
                seqa = seq.toannotation()
                for s in yielded_seqs:
                    if s.contains(seqa):
                        # seq is useless...
                        yield_seq = False
                        break
                if yield_seq:
                    yielded_seqs.append(create_set(seqa))
                    yield seq

        # try without relations
        seq = InductiveSequence(
            overapprox_set(
                self, EM, S, errs0.toassert(), target, None, L
            ).as_assert_annotation()
        )

        if is_seq_inductive(seq, self, L):
            # check if seq is a subset of some previously yielded sequence
            yield_seq = True
            seqa = seq.toannotation()
            for s in yielded_seqs:
                if s.contains(seqa):
                    # seq is useless...
                    yield_seq = False
                    break
            if yield_seq:
                yield seq

    def _last_k_iteration_paths(self, L, k=0):
        """ Obtain the paths that correspond to the last k iterations of the loop """
        is_error_loc = L.cfa().is_err
        exits = [p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())]
        if k == 0:
            return exits
        loop_paths = L.paths()
        paths = [e.edges() for e in exits]
        while k > 0:
            # we loose annotations if any -- but there should be none in this case
            paths = [l.edges() + s for l in loop_paths for s in paths]
            k -= 1
        return [AnnotatedCFAPath(p) for p in paths]

    def _last_k_iterations_states(self, L, k=0):
        assert k >= 0, k

        create_set = self.create_set
        paths = self._last_k_iteration_paths(L, k)
        sets = []
        for p in paths:
            r = check_paths(self, [p])
            if not r.ready:
                continue

            tmp = create_set()
            tmp.add(r.ready)
            sets.append(tmp)
        assert sets
        return sets

    def _initial_sets_from_iters(self, E, L: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """
        create_set = self.create_set
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        precondition = lambda s: self.unwind_iteration(L, s)
        rels = lambda s, l=None: set(list(get_const_cmp_relations(s)) + list(get_var_relations(s, l)))
        approx = lambda s, a=None:\
        overapprox_set(
            self, getGlobalExprManager(), s, E, s, a, L
        )

        S0 = self._initial_sets_from_exits(E, L)
        if not S0:
            return None
        sets = set()
        for s0 in S0:
            R0 = rels(s0.get_se_state())
            for s1 in precondition(s0.get_se_state()):
                R1 = rels(s1, s0)
                for s2 in precondition(s1):
                    R2 = rels(s2, create_set(s1))
                    for rel in R1.intersection(R2):
                        if not intersection(s0, rel).is_empty():
                            A = approx(intersection(s0, *R0), create_set(rel))
                            if not A.is_empty():
                                sets.add(A)
                            else:
                                A = approx(intersection(s0, *R0))
                                if not A.is_empty():
                                    sets.add(A)
                                else:
                                    sets.add(approx(s0))
        if sets:
            return [approx(union(*sets))] if len(sets) > 1 else list(sets)
        return [approx(s0) for s0 in S0]

    def _initial_sets_from_exits(self, E, L: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        cE = complement(E)
        tmpsets = self._last_k_iterations_states(L, k = 0)
        sets = []
        for tmp in tmpsets:
            tmp.intersect(cE)
            if not tmp.is_empty():
                sets.append(tmp)
        return sets

    def _match_included_indsets(self, isets, sets):
        create_set = self.create_set
        # replace every set in 'sets' with an inductive set that we already have
        # if the IS already includes the set
        newsets = []
        union_matched = self.options.union_matched
        for s in sets:
            cov = [
                I for I in isets if intersection(I.I, s).is_empty() and I.I.contains(s)
            ]
            if cov:
                dbg("Matched stored inductive sequences")
                S = create_set() if union_matched else None
                for I in cov:
                    if union_matched:
                        # and not S.contains(I.I):
                        # todo: could the inclusion check break inferring relations from path condition? Probably yes.
                        S.add(I.I)
                    else:
                        newsets.append(I.I)
                    # remove the matched set from inductive sets
                # l = len(isets)
                # isets.remove(I)
                # assert l - 1 == len(isets), "Did not pop the element"
                newsets.append(S)
            else:
                newsets.append(s)
        return newsets or None

    def initial_sets_from_exits(self, E, L: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """

        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        sets = self._initial_sets_from_exits(E, L)
        # try to match the sets with inductive sets that we already have
        isets = self.inductive_sets.get(L.header())
        if isets is None:
            return sets

        return self._match_included_indsets(isets, sets)

    def initial_sets_from_last_iters(self, E, L: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """

        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is inductive
        sets = self._initial_sets_from_iters(E, L)
        # try to match the sets with inductive sets that we already have
        isets = self.inductive_sets.get(L.header())
        if isets is None:
            return sets

        return self._match_included_indsets(isets, sets)


    def initial_sets_from_is(self, E, L):
        # get the inductive sets that we have created for this header.
        # Since we go iteration over iteration, adding this sequence
        # to the previous ones must yield an inductive sequence
        isets = self.inductive_sets.get(L.header())
        if isets is None:
            return None

        exit_sets = self._initial_sets_from_exits(E, L)

        dbg("Checking inductive sets that we have")
        sets = []
        included_sets = []
        # newisets = []
        for I in isets:
            if intersection(I.I, E).is_empty():
                sets.append(I.I)
                if exit_sets and I.I.contains_any(*exit_sets):
                    included_sets.append(I.I)
        #    else:
        #        newisets.append(I)
        # self.inductive_sets[L.header()] = newisets

        # use the sets that include some of the sets created for exit sets
        if included_sets:
            sets = included_sets
        if sets:
            dbg("Matched stored inductive sequences")
            if self.options.union_matched:
                return [union(*sets)]
            return sets
        return None

    def add_invariant(self, loc, inv):
        invs = self.invariant_sets.setdefault(loc, [])
        invs.append(inv.to_assume(getGlobalExprManager()))
        # FIXME: check that the invariant gives us a new information
        # I = create_set() # FIXME: cache the union of invariants
        # I.add(invs)
        # I.intersect()
        print_stdout(f"{inv} holds on {loc}", color="BLUE")

    def add_inductive_set(self, loc, S):
        I = InductiveSet(self.create_set(S))
        self.inductive_sets.setdefault(loc, []).append(I)

    def fold_loop(self, loc, L: LoopInfo, unsafe, loop_hit_no):
        print_stdout(
            f"========== Folding loop {loc} ({loop_hit_no} time) ===========",
            color="white",
        )
        if __debug__:
            _dump_inductive_sets(self, loc)

        assert unsafe, "No unsafe states, we should not get here at all"
        create_set = self.create_set

        dbg(f"Getting initial sequence for loop {loc}")
        seqs0, errs0 = self.get_initial_seqs(unsafe, L, loop_hit_no)
        if not seqs0:
            print_stdout(
                f"Failed getting initial inductive sequence for loop {loc}", color="red"
            )
            # FIXME: the initial element must be inductive, otherwise we do not know whether
            # an error state is unreachable from it...
            return False
        assert seqs0

        if __debug__:
            for seq0 in seqs0:
                assert intersection(
                    create_set(seq0.toannotation()), errs0.toassert()
                ).is_empty(), "Initial sequence contains error states"

        # now we do not support empty sequences
        assert all(map(lambda s: s is not None, seqs0)), "A sequence is none"

        sequences = seqs0
        E = create_set(errs0.toassert())

        dbg(
            f"Folding loop {loc} with errors:\n  {errs0}\nand starting sets:\n{seqs0}",
            color="gray",
        )

        # a good length is at least 3 to make the relations to previous state
        # take effect. If we start creating starting inductive sets
        # from several states, the length could decrease to 2
        # max_seq_len = max(3, 2 * len(L.paths()))
        max_seq_len = 2 * len(L.paths())
        while True:
            print_stdout(
                f"Got {len(sequences)} abstract path(s) of loop " f"{loc}",
                color="dark_blue",
            )
            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to find that out?
            for n, seq in enumerate(sequences):
                assert seq, sequences
                S = seq.toannotation(True)
                # FIXME: cache CTI's to perform fast checks of non-inductivness.
                res, _ = self.check_loop_precondition(L, S)
                if res is Result.SAFE:
                    # store the other sequences for further processing
                    for i, oseq in enumerate(sequences):
                        if i == n:
                            continue
                        self.add_inductive_set(loc, oseq.toannotation(True))

                    # add the current sequence as invariant
                    self.add_invariant(loc, seq.toannotation(False))
                    return True

            extended = []
            for seq in sequences:
                assert seq, sequences

                print_stdout(
                    f"Extending a sequence of len {len(seq) if seq else 0}...",
                    color="gray",
                )
                dbg(f"{seq}", color="dark_blue")

                if __debug__:
                    assert intersection(
                        create_set(seq.toannotation(True)), errs0.toassert()
                    ).is_empty(), "Sequence is not safe"

                if len(seq) >= max_seq_len:
                    dbg("Give up extending the sequence, it is too long")
                    self.add_inductive_set(loc, seq.toannotation(True))
                    continue

                # FIXME: we usually need seq[-1] as annotation, or not?
                for A in self.extend_seq(seq, E, L):
                    dbg(f"Extended with: {A}", color="brown")
                    tmp = seq.copy()
                    tmp.append(A.as_assert_annotation(), None)
                    if __debug__:
                        assert is_seq_inductive(
                            tmp, self, L
                        ), "Extended sequence is not inductive"

                    extended.append(tmp)
                dbg("Extending the sequence finished")

            if not extended:
                # seq not extended... it looks that there is no safe invariant
                # FIXME: could we use it for annotations?
                print_stdout("Failed extending any sequence", color="orange")
                print_stdout(
                    f"========== Folding loop {loc} finished (unsuccessfully) ===========",
                    color="orange",
                )
                return False  # fall-back to unwinding

            sequences = extended

    def is_loop_header(self, loc: CFA.Location):
        assert isinstance(loc, CFA.Location)
        return loc in self.get_loop_headers()

    def check(self, onlyedges=None):
        # the initial error path that we check
        loc = self.location
        em = getGlobalExprManager()
        notA = self.assertion.assume_not(em)
        for edge in onlyedges if onlyedges else loc.predecessors():
            state = self.ind_executor().create_clean_state()
            state.apply_postcondition(notA)
            self.queue_state(
                BSEContext(edge, state, errdescr=AssertFailError(f"{loc} reachable."))
            )

        opt_fold_loops = self.getOptions().fold_loops
        while True:
            bsectx = self.get_next_state()
            if bsectx is None:
                return (
                    Result.UNKNOWN if (self.problematic_states) else Result.SAFE
                ), self.problematic_paths_as_result()

            # ldbgv("Main loop state: {0}", (bsectx,))
            r, pre = self.precondition(bsectx)
            if r is Result.SAFE:
                assert pre is None, "Feasible precondition for infeasible error path"
                continue  # infeasible path
            if r is Result.UNSAFE:  # real error
                return r, pre
            #  the error path is feasible, but the errors may not be real
            assert r is Result.UNKNOWN
            if opt_fold_loops:
                # is this a path starting at a loop header?
                fl = bsectx.path[0].source()
                if self.is_loop_header(fl):
                    # check whether we are not told to give up when hitting this loop this time
                    loc_hits = bsectx.loc_hits
                    lnm = loc_hits[fl] = loc_hits.get(fl, 0) + 1
                    mlh = self._max_loop_hits
                    if mlh and lnm > mlh:
                        dbg("Hit limit of visits to a loop in this context")
                        return Result.UNKNOWN, pre

                    if fl not in self.no_sum_loops:
                        if self.handle_loop(fl, pre, lnm):
                            dbg(
                                f"Path with loop {fl} proved safe",
                                color="dark_green",
                            )
                        else:
                            self.extend_state(bsectx, pre)
                        continue
            self.extend_state(bsectx, pre)

        raise RuntimeError("Unreachable")


class BSELF:
    """
    The main class for BSE and BSELF (BSE is a BSELF without loop folding)
    that divides and conquers the tasks.
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
            if F.is_undefined():
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
            checker = BSELFChecker(
                loc,
                A,
                self.program,
                self.programstructure,
                self.options,
                invariants=self.invariants,
            )
            result, states = checker.check()
            self.stats.add(checker.stats)
            if result is Result.UNSAFE:
                # FIXME: report the error from bsecontext
                print_stdout(
                    f"{states.get_id()}: [assertion error]: {loc} reachable.",
                    color="redul",
                )
                print_stdout(str(states), color="wine")
                print_stdout("Error found.", color="redul")
                self.stats.errors += 1
                return result
            if result is Result.SAFE:
                print_stdout(
                    f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                )
            elif result is Result.UNKNOWN:
                print_stdout(f"Checking {A} at {loc} was unsuccessful.", color="yellow")
                has_unknown = True
                assert checker.problematic_states, "Unknown with no problematic paths?"
                for p in checker.problematic_states:
                    report_state(self.stats, p)

        if has_unknown:
            print_stdout("Failed deciding the result.", color="orangeul")
            return Result.UNKNOWN

        print_stdout("No error found.", color="greenul")
        return Result.SAFE
