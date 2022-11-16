from typing import Optional, List, Sized

from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bse import (
    check_paths,
    BackwardSymbolicInterpreter as BaseBSE,
    report_state,
)
from slowbeast.bse.bsectx import BSEContext
from slowbeast.bse.inductivesequence import InductiveSequence
from slowbeast.bse.inductiveset import InductiveSet
from slowbeast.bse.loopinfo import LoopInfo
from slowbeast.bse.options import BSELFOptions
from slowbeast.cfkind.annotatedcfa import AnnotatedCFAPath
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.cfkind.overapproximations import overapprox_set
from slowbeast.cfkind.relations import get_const_cmp_relations, get_var_relations
from slowbeast.core.errors import AssertFailError
from slowbeast.domains.symbolic_helpers import to_c_expression
from slowbeast.solvers.symcrete import global_expr_mgr
from slowbeast.symexe.statesset import StatesSet, union, intersection, complement
from slowbeast.util.debugging import (
    dbg,
    ldbg,
    print_stdout,
    inc_print_indent,
    dec_print_indent,
    ldbgv,
    dbg_sec,
)


def _dump_inductive_sets(checker, loc, fn=dbg) -> None:
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


def is_seq_inductive(seq, loopinfo: LoopInfo) -> bool:
    return loopinfo.set_is_inductive(seq.as_set())


def is_set_inductive(S, loopinfo: LoopInfo) -> bool:
    return loopinfo.set_is_inductive(S)


def _check_set_is_inductive_towards(executor, S: StatesSet, loopinfo, target) -> bool:
    # FIXME: this is a workaround until we support nondet() calls in lazy execution
    r = check_paths(executor, loopinfo.paths(), pre=S, post=union(S, target))
    if r.errors:
        dbg(
            "FIXME: pre-image is not inductive cause we do not support "
            "nondets() in lazy execution yet"
        )
        return False
    # --- workaround ends here...
    # if S.is_empty():
    #    dbg("Starting sequence is empty")
    #    return False
    return True


def overapprox_state(executor, state, errset: StatesSet, target, loopinfo):
    state_as_set = state if isinstance(state, StatesSet) else executor.create_set(state)

    if not _check_set_is_inductive_towards(executor, state_as_set, loopinfo, target):
        return

    # add relations
    for rel in get_const_cmp_relations(state_as_set.get_se_state()):
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

        state_as_set.intersect(rel)
        assert (
            not state_as_set.is_empty()
        ), f"Added realtion {rel} rendered the set infeasible\n{state_as_set}"
        assert intersection(
            state_as_set, errset
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

    yield from _overapprox_with_assumptions(
        errset, loopinfo, state_as_set, executor, state, target
    )

    # try without any relation
    # assert not S.is_empty(), "Infeasible states given to overapproximate"
    yield overapprox_set(
        executor, state.expr_manager(), state_as_set, errset, target, None, loopinfo
    )


def _overapprox_with_assumptions(
    errset, loopinfo, state_as_set, executor, state, target
):
    """
    Infer a set of relations that hold in S and over-approximate the set
    w.r.t. these relations.
    """
    # precise prestates of this state
    relations = set(get_var_relations([state_as_set.get_se_state()], prevsafe=target))
    if not relations:
        return
    yield from _yield_overapprox_with_assumption(
        errset, loopinfo, state_as_set, executor, relations, state, target
    )


def _yield_overapprox_with_assumption(
    errset, loopinfo, state_as_set, executor, rels, state, target
):
    create_set = executor.create_set
    for rel in rels:
        ldbg("  Using assumption {0}", (rel,))
        assumptions = create_set(rel)
        assert not intersection(
            assumptions, state_as_set
        ).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            assumptions, state_as_set, errset
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"
        assert not state_as_set.is_empty(), "Infeasible states given to overapproximate"
        yield overapprox_set(
            executor,
            state.expr_manager(),
            state_as_set,
            errset,
            target,
            assumptions,
            loopinfo,
        )


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
        programstructure: Optional[ProgramStructure],
        opts: BSELFOptions,
        invariants=None,
        indsets=None,
        max_loop_hits=None,
    ) -> None:
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
        self.max_seq_len = None

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

    def execute_path(self, path, from_init: bool = False, invariants=None):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        if from_init:
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
        if from_init and earl:
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

    def unwind(self, loc, errpre, maxk=None) -> int:
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
                if r is Result.UNSAFE:
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

    def handle_loop(self, loc, errpre, loop_hit_no: int) -> bool:
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

        assert errpre, "No unsafe states, we should not get here at all"
        unsafe = [errpre]

        # first try to unroll it in the case the loop is easy to verify
        if loop_hit_no == 1:
            maxk = 2  # unroll the loop only once
            dbg_sec(f"Unwinding the loop {maxk} iterations")
            # FIXME: use unwind_iteration
            res = self.unwind(loc, errpre, maxk=maxk)
            dbg_sec()
            if res is Result.SAFE:
                if self.options.add_unwind_invariants:
                    self.add_invariant(
                        loc, complement(self.create_set(errpre)).as_assume_annotation()
                    )
                print_stdout(f"Loop {loc} proved by unwinding", color="GREEN")
                return True
            if res is Result.UNSAFE:
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

    def _extend_one_step(self, loop, target):
        r = check_paths(self, loop.paths(), post=target)
        if not r.ready:  # cannot step into this frame...
            dbg("Infeasible frame...")
            # FIXME: remove this sequence from INV sets
            return None
        for s in r.killed():
            dbg("Killed a state")
            report_state(self.stats, s)
            return None
        return r.ready

    def _extend_seq(self, seq, E, L):
        """
        Compute the precondition for reaching S and overapproximate it

        S - target states
        E - error states
        """
        assert seq
        if self._target_is_whole_seq:
            target = seq[-1]
        else:
            target = seq.as_set()

        prestates = self._extend_one_step(L, target)
        if not prestates:
            dbg("Cannot step into seqence...")
            # this one can be removed from inductive sets
            # xxx: target clearly describes a set of states that are
            # unreachable in the state space. Couldn't we use it somehow?
            loc = L.header()
            IS = self.inductive_sets.get(loc)
            if IS:
                tmp = seq.as_set()
                self.inductive_sets[loc] = [I for I in IS if not tmp.contains(I.I)]
            return

        toyield = []
        for s in prestates:
            if not intersection(E, s).is_empty():
                dbg("Pre-image is not safe...")
                # TODO: should we try the intersection with complement of E?
                continue
            for A in overapprox_state(self, s, E, target, L):
                if A is None:
                    dbg("Overapproximation failed...")
                    continue

                if __debug__:
                    assert (
                        seq is None or intersection(A, E).is_empty()
                    ), f"Overapproximation is not safe: {A}"

                # todo: check w.r.t seq?
                if target.contains(A):
                    dbg("Did not extend (got included elem...)")
                    continue

                # keep only the overapproximations with the most models
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

    def get_initial_seqs(
        self, E: StatesSet, L: LoopInfo, loop_hit_no: int
    ) -> Optional[List[InductiveSequence]]:
        S = E.copy()
        S.complement()

        if S.is_empty():
            return None
        # FIXME: we do not check and return inductive complements as the init
        # seq right now as that allows also inductive sets with array variables
        # that we cannot handle # (e.g., string-2-false.c test).
        seqs = []
        if loop_hit_no == 1:
            dbg("... (getting sis for the 1st hit of the loop)")
            Is = self.initial_sets_from_exits(E, L)
            # cont. of the workaround -- the same problem. The set may not
            # be inductive due to dynamic inputs or array variables.
            # see, e.g., array_3-2.c
            # assert Is, "Failed getting sequence for first visit"
        else:
            dbg("... (joining with previously unfinished sequences)")
            Is = self.initial_sets_from_is(E, L)
        if Is:
            for s in Is:
                # should be inductive from construction - xxx: if it does
                # not contain array variables, that's why we check
                # explicitly for the inductiveness
                # assert is_seq_inductive(s, L), f"seq is not inductive: {s}"
                if is_set_inductive(s, L):
                    dbg("... (got first IS)")
                    seqs.append(InductiveSequence(s))

        # reduce and over-approximate the initial sequence
        if seqs:
            tmp = []
            print_stdout(
                f"Got {len(seqs)} starting inductive sequence(s)", color="dark_blue"
            )
            for seq in seqs:
                tmp.extend(self.overapprox_init_seq(seq, E, L))
            if tmp:
                seqs = tmp

        # inductive sequence is either inductive now, or it is None and we'll
        # use non-inductive E
        return seqs or None

    def overapprox_init_seq(self, seq0, unsafe: StatesSet, L: LoopInfo):
        assert is_seq_inductive(seq0, L), "seq is not inductive"
        dbg("Overapproximating initial sequence")
        dbg(str(seq0))

        target = seq0[-1]
        S = seq0.as_set().copy()  # we're going to change S
        # assert not S.is_empty(), f"Starting sequence is infeasible!: {seq0}"
        EM = global_expr_mgr()

        yielded_seqs = []
        for A in overapprox_state(self, S, unsafe, S, L):
            if is_set_inductive(A, L):
                # check if seq is a subset of some previously yielded sequence
                yield_seq = True
                for s in yielded_seqs:
                    if s.contains(A):
                        # seq is useless...
                        yield_seq = False
                        break
                if yield_seq:
                    yielded_seqs.append(A)
                    yield InductiveSequence(A)

        # try without relations
        seq = InductiveSequence(overapprox_set(self, EM, S, unsafe, target, None, L))

        if is_seq_inductive(seq, L):
            # check if seq is a subset of some previously yielded sequence
            yield_seq = True
            for s in yielded_seqs:
                if s.contains(seq.as_set()):
                    # seq is useless...
                    yield_seq = False
                    break
            if yield_seq:
                yield seq

    def _last_k_iteration_paths(self, L, k: int = 0):
        """Obtain the paths that correspond to the last k iterations of the loop"""
        is_error_loc = L.cfa().is_err
        exits = [p for p in L.get_exit_paths() if not is_error_loc(p.last_loc())]
        if k == 0:
            return exits
        loop_paths = L.paths()
        paths = [e.edges() for e in exits]
        while k > 0:
            # we loose annotations if any -- but there should be none in this
            # case
            paths = [l.edges() + s for l in loop_paths for s in paths]
            k -= 1
        return [AnnotatedCFAPath(p) for p in paths]

    def _last_k_iterations_states(self, L, k: int = 0):
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
        return sets

    def _initial_sets_from_exits(self, errs: StatesSet, loopinfo: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """
        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is
        # inductive
        cE = complement(errs)
        tmpsets = self._last_k_iterations_states(loopinfo, k=0)
        sets = []
        for tmp in tmpsets:
            tmp.intersect(cE)
            if not tmp.is_empty():
                sets.append(tmp)
        return sets

    def _match_included_indsets(self, isets, sets, E):
        create_set = self.create_set
        # replace every set in 'sets' with an inductive set that we already have
        # if the IS already includes the set
        newsets = []
        union_matched = self.options.union_matched
        for s in sets:
            # gather the sets that subsume 's' and are disjunctive with unsafe
            # states
            cov = [I for I in isets if intersection(E, s).is_empty() and I.includes(s)]
            if cov:
                dbg("Matched stored inductive sequences")
                S = create_set() if union_matched else None
                for I in cov:
                    if union_matched:
                        # todo: could the inclusion check weaken inferring
                        # relations from path condition? Probably yes.
                        S.add(I.I)
                    else:
                        newsets.append(I.I)
                newsets.append(S)
            else:
                newsets.append(s)
        return newsets or None

    def initial_sets_from_exits(self, E: StatesSet, L: LoopInfo):
        """
        Strengthen the initial sequence through obtaining the
        last safe iteration of the loop.
        """

        # execute the safe path that avoids error and then jumps out of the loop
        # and also only paths that jump out of the loop, so that the set is
        # inductive
        sets = self._initial_sets_from_exits(E, L)
        # try to match the sets with inductive sets that we already have
        isets = self.inductive_sets.get(L.header())
        if isets is None:
            return sets

        return self._match_included_indsets(isets, sets, E)

    def initial_sets_from_is(self, E: StatesSet, L: LoopInfo):
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
        for I in isets:
            if intersection(I.I, E).is_empty():
                sets.append(I.I)
                if exit_sets and I.includes_any(*exit_sets):
                    included_sets.append(I.I)

        # use the sets that include some of the sets created for exit sets
        if included_sets:
            sets = included_sets
        if sets:
            dbg("Matched stored inductive sequences")
            if self.options.union_matched:
                return [union(*sets)]
            return sets
        return None

    def add_invariant(self, loc, inv) -> None:
        invs = self.invariant_sets.setdefault(loc, [])
        invs.append(inv.to_assume(global_expr_mgr()))
        # FIXME: check that the invariant gives us a new information
        # I = create_set() # FIXME: cache the union of invariants
        # I.add(invs)
        # I.intersect()
        dbgloc = loc.elem()[0].get_metadata("dbgloc")
        if dbgloc:
            print_stdout(
                f"{to_c_expression(inv.get_cannonical().unwrap())} holds at line {dbgloc[1]}",
                color="BLUE",
            )
        else:
            print_stdout(
                f"{to_c_expression(inv.get_cannonical().unwrap())} holds at {loc}",
                color="BLUE",
            )

    def add_inductive_set(self, loc, S) -> None:
        I = InductiveSet(self.create_set(S))
        self.inductive_sets.setdefault(loc, []).append(I)

    def fold_loop(self, loc, L: LoopInfo, unsafe: Sized, loop_hit_no: int) -> bool:
        print_stdout(
            f"========== Folding loop {loc} ({loop_hit_no} time) ===========",
            color="white",
        )
        if __debug__:
            _dump_inductive_sets(self, loc)

        dbg(f"Getting initial sequence for loop {loc}")

        assert unsafe, "No unsafe states, we should not get here at all"
        assert len(unsafe) == 1, "One path raises multiple unsafe states"
        E = self.create_set(unsafe[0])
        seqs0 = self.get_initial_seqs(E, L, loop_hit_no)
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
                    seq0.as_set(), E
                ).is_empty(), "Initial sequence contains error states"

        # now we do not support empty sequences
        assert all(map(lambda s: s is not None, seqs0)), "A sequence is none"

        sequences = seqs0

        dbg(
            f"Folding loop {loc} with errors:\n  {E}\nand starting sets:\n{seqs0}",
            color="gray",
        )

        # a good length is at least 3 to make the relations to previous state
        # take effect. If we start creating starting inductive sets
        # from several states, the length could decrease to 2
        # max_seq_len = max(3, 2 * len(L.paths()))
        max_seq_len = self.max_seq_len or (2 * len(L.paths()))
        while True:
            print_stdout(
                f"Got {len(sequences)} abstract path(s) of loop {loc}",
                color="dark_blue",
            )

            # store the sequences for further re-use
            for seq in sequences:
                # FIXME: use an incremental solver for each sequence
                # and also for the inductive sets (in those, we use incremental solver only
                # for the complement and we do not copy it - always create it from scratch).
                # So, in fact, we could save just the sequences...
                self.add_inductive_set(loc, seq.as_assert_annotation())

            # FIXME: check that all the sequences together cover the input paths
            # FIXME: rule out the sequences that are irrelevant here? How to
            # find that out?
            for _, seq in enumerate(sequences):
                assert seq, sequences
                S = seq.as_assert_annotation()
                res, _ = self.check_loop_precondition(L, S)
                if res is Result.SAFE:
                    # add the current sequence as invariant
                    self.add_invariant(loc, seq.as_assume_annotation())
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
                        seq.as_set(), E
                    ).is_empty(), "Sequence is not safe"

                if len(seq) >= max_seq_len:
                    dbg("Give up extending the sequence, it is too long")
                    continue

                # FIXME: we usually need seq[-1] as annotation, or not?
                for A in self.extend_seq(seq, E, L):
                    dbg(f"Extended with: {A}", color="brown")
                    tmp = seq.copy()
                    tmp.append(A)
                    if not is_seq_inductive(tmp, L):
                        assert False, "Extended sequence is not inductive"
                        continue

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

    def init_checker(self, onlyedges=None) -> None:
        # the initial error path that we check
        loc = self.location
        em = global_expr_mgr()
        notA = self.assertion.assume_not(em)
        for edge in onlyedges if onlyedges else loc.predecessors():
            state = self.ind_executor().create_clean_state()
            state.apply_postcondition(notA)
            self.queue_state(
                BSEContext(edge, state, errdescr=AssertFailError(f"{loc} reachable."))
            )

    def do_step(self):
        bsectx = self.get_next_state()
        if bsectx is None:
            return (
                Result.UNKNOWN if self.problematic_states else Result.SAFE
            ), self.problematic_paths_as_result()
        return self._do_step(bsectx)

    def _do_step(self, bsectx: BSEContext):
        assert bsectx is not None
        r, pre = self.precondition(bsectx)
        if r is Result.SAFE:
            assert pre is None, "Feasible precondition for infeasible error path"
            return None, None  # infeasible path
        if r is Result.UNSAFE:  # real error
            if self.options.replay_errors:
                found_error = pre.get_error()
                s = self.replay_state(pre)
                if s.has_error() and found_error.type() == s.get_error().type():
                    # FIXME: check that even the instructions match!
                    r = Result.UNSAFE
                else:
                    dbg(
                        f"Found error: {found_error} was not confirmed, "
                        f"got: {s.status()} (detail: {s.status_detail()})"
                    )
                    r = Result.UNKNOWN
                if r is Result.UNSAFE:  # real error
                    return r, s
                dbg("Replaying error failed")
                s.set_killed("Replay failed")
                self.problematic_states.append(s)
            else:
                return r, pre
        #  the error path is feasible, but the errors may not be real
        assert r is Result.UNKNOWN
        if self.get_options().fold_loops:
            # is this a path starting at a loop header?
            fl = bsectx.path[0].source()
            if self.is_loop_header(fl):
                # check whether we are not told to give up when hitting this
                # loop this time
                loc_hits = bsectx.loc_hits
                lnm = loc_hits[fl] = loc_hits.get(fl, 0) + 1
                if fl not in self.no_sum_loops:
                    if self.handle_loop(fl, pre, lnm):
                        dbg(
                            f"Path with loop {fl} proved safe",
                            color="dark_green",
                        )
                        return None, None  # we're done with this path
                mlh = self._max_loop_hits
                if mlh and lnm >= mlh:
                    dbg("Hit limit of visits to a loop in this context")
                    return Result.UNKNOWN, pre
        newstates = self.extend_state(bsectx, pre)
        for s in newstates:
            self.queue_state(s)
        return None, None

    def check(self, onlyedges=None):
        # the initial error path that we check
        self.init_checker(onlyedges)

        do_step = self.do_step
        while True:
            res, pre = do_step()
            if res is not None:
                return res, pre
