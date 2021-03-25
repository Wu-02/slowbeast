from slowbeast.util.debugging import print_stdout, dbg, dbg_sec, ldbg, ldbgv

from slowbeast.kindse.annotatedcfa import AnnotatedCFAPath
from slowbeast.kindse.naive.naivekindse import Result
from slowbeast.kindse import KindSEOptions
from slowbeast.symexe.statesset import intersection, union, complement
from slowbeast.symexe.symbolicexecution import SEStats
from slowbeast.analysis.loops import Loop
from slowbeast.kindse.programstructure import ProgramStructure

from slowbeast.symexe.annotations import AssertAnnotation

from slowbeast.solvers.solver import getGlobalExprManager

from .bse import BackwardSymbolicInterpreter as BaseBSE, BSEContext, report_state, check_paths
from slowbeast.kindse.inductivesequence import InductiveSequence
from slowbeast.kindse.overapproximations import overapprox_set
from slowbeast.kindse.relations import get_const_cmp_relations, get_var_relations
from .inductiveset import InductiveSet
from .loopinfo import LoopInfo


class BSELFOptions(KindSEOptions):
    def __init__(self, copyopts=None):
        super().__init__(copyopts)
        if copyopts:
            self.fold_loops = copyopts.fold_loops = True
            self.target_is_whole_seq = copyopts.target_is_whole_seq = True
        else:
            self.fold_loops = True
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
    create_set = executor.create_set
    S = create_set(s)

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

    # add relations
    for rel in get_const_cmp_relations(S.get_se_state()):
        ldbg("  Adding relation {0}", (rel,))
        S.intersect(rel)
        assert not S.is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            S, E
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

    for rel in get_var_relations([S.get_se_state()], prevsafe=target):
        ldbg("  Using assumption {0}", (rel,))
        assumptions = create_set(rel)
        assert not intersection(assumptions, S).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            assumptions, S, E
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

        assert not S.is_empty(), "Infeasible states given to overapproximate"
        yield overapprox_set(executor, s.expr_manager(),
                             S, E, target, assumptions, L)

    #try without any relation
    assert not S.is_empty(), "Infeasible states given to overapproximate"
    yield overapprox_set(executor, s.expr_manager(), S, E, target, None, L)


def is_seq_inductive(seq, executor, L : LoopInfo):
    return L.set_is_inductive(executor.create_set(seq.toannotation()))

class BSELFChecker(BaseBSE):
    """
    An executor that recursively checks the validity of one particular assertion.
    In particular, it checks whether the given assertion holds when entering the
    given location.
    It inherits from BaseBSE to have the capabilities to execute paths.
    """

    def __init__(self, loc, A, program, programstructure, opts,
                 invariants=None, indsets=None):
        super().__init__(
            program,
            ohandler=None,
            opts=opts,
            programstructure=programstructure,
            invariants=invariants
        )
        assert isinstance(opts, BSELFOptions), opts
        self.program = program
        self.location = loc
        self.assertion = A

        self.options = opts
        self._target_is_whole_seq = opts.target_is_whole_seq

        self.create_set = self.ind_executor().create_states_set
        self.get_loop_headers= programstructure.get_loop_headers

        self.loop_info = {}

        # inductive sets for deriving starting sequences
        self.inductive_sets = indsets or {}

        if __debug__ and invariants:
            dbg("Have these invariants at hand:")
            for loc, invs in invariants.items():
                dbg(f"  @ {loc}: {invs}")

        self.no_sum_loops = set()

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
        dbg_sec(f"Checking if {A} holds on {loc}")

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

            s = executor.createCleanState()
            states = [s]

            ldbgv("Executing path: {0}", (path,), fn=self.reportfn, color="orange")

        assert all(
            map(lambda s: not s.getConstraints(), states)
        ), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.execute_annotated_path(states, path, invariants)
        self.stats.paths += 1

        earl = r.early
        if fromInit and earl:
            # this is an initial path, so every error is taken as real
            errs = r.errors or []
            for e in (e for e in earl if e.hasError()):
                errs.append(e)
            r.errors = errs

        return r


    def handle_loop(self, loc, errpre):
        assert (
            loc not in self.no_sum_loops
        ), "Handling a loop that should not be handled"

        assert errpre, "No unsafe states, we should not get here at all"
        unsafe = [errpre]

        #   # first try to unroll it in the case the loop is easy to verify
       #maxk = 15
       #dbg_sec(f"Unwinding the loop {maxk} steps")
       #res, unwoundloop = self.unwind([path.copy()], maxk=maxk)
       #dbg_sec()
       #if res is Result.SAFE:
       #   print_stdout(
       #       f"Loop {loc} proved by unwinding", color="GREEN"
       #   )
       #   return res, []
       #elif res is Result.UNSAFE:
       #   self.no_sum_loops.add(loc)
       #   return res, [path]  # found an error

        L = self.get_loop(loc)
        if L is None:
            print_stdout("Was not able to construct the loop info")
            print_stdout(f"Falling back to unwinding loop {loc}", color="BROWN")
            self.no_sum_loops.add(loc)
            #return Result.UNKNOWN, unwoundloop
            return False

        return self.fold_loop(loc, L, unsafe)

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
            for A in overapprox(self, s, E, target, L):
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

    def get_simple_initial_seqs(self, unsafe : list, L : Loop):
        E = self.create_set(unsafe[0])

        S = E.copy()
        S.complement()
        target0 = S.copy()

        errs0 = InductiveSequence.Frame(E.as_assert_annotation(), None)
        seq0 = InductiveSequence(S.as_assert_annotation(), None)
        if S.is_empty():
            return target0, None, errs0
        if not is_seq_inductive(seq0, self, L):
            dbg("... (complement not inductive)")
            seqs = []
            Is = self.initial_sets_from_is(E, L)
            if not Is:
                dbg("... (no match in inductive sets)")
                Is = self.initial_sets_from_exits(E, L)
            if Is:
                for s in (InductiveSequence(I.as_assert_annotation(), None) for I in Is):
                    dbg("... (got first IS)")
                    # should be inductive from construction
                    assert is_seq_inductive(s, self, L), f'seq is not inductive: {s}'
                    seqs.append(s)
                   #if is_seq_inductive(s, self, L):
                   #    seqs.append(s)
            seqs = seqs or None
        else:
            dbg("... (complement is inductive)")
            seqs = [seq0]

        return target0, seqs, errs0

    def get_initial_seqs(self, unsafe : list, L : Loop):
        assert len(unsafe) == 1, "One path raises multiple unsafe states"

        target0, seqs, errs0 = self.get_simple_initial_seqs(unsafe, L)
        # reduce and over-approximate the initial sequence
        if seqs:
            tmp = []
            dbg(f'Got {len(seqs)} starting inductive sequence(s)')
            for seq in seqs:
                tmp.extend(self.overapprox_init_seq(seq, errs0, L))
            if tmp:
                seqs = tmp

        # inductive sequence is either inductive now, or it is None and we'll use non-inductive E
        return target0, seqs, errs0

    def overapprox_init_seq(self, seq0, errs0, L):
        assert is_seq_inductive(seq0, self, L), "seq is not inductive"

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
            assert not S.is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
            assert intersection(
                S, unsafe
            ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

        assumptions = create_set()
        for rel in get_var_relations([S.get_se_state()], prevsafe=target):
            ldbg("  Using assumption {0}", (rel,))
            assumptions.intersect(rel)
            assert not intersection(assumptions, S).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
            assert intersection(
                assumptions, S, unsafe
            ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

            seq = InductiveSequence(
                overapprox_set(
                    self, EM, S, errs0.toassert(), target,
                    assumptions, L
                ).as_assert_annotation()
            )

            if is_seq_inductive(seq, self, L):
                yield seq

        # try without relations
        seq = InductiveSequence(
            overapprox_set(
                self, EM, S, errs0.toassert(), target,
                None, L
            ).as_assert_annotation()
        )

        if is_seq_inductive(seq, self, L):
            yield seq

    def initial_sets_from_exits(self, E, L: Loop):
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
            if not r.ready:
                continue

            tmp = create_set()
            tmp.add(r.ready)
            tmp.intersect(cE)
            if not tmp.is_empty():
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

    def fold_loop(self, loc, L: Loop, unsafe):
        dbg(f"========== Folding loop {loc} ===========")
        if __debug__:
            _dump_inductive_sets(self, loc)

        assert unsafe, "No unsafe states, we should not get here at all"
        create_set = self.create_set

        dbg(f"Getting initial sequence for loop {loc}")
        target0, seqs0, errs0 = self.get_initial_seqs(unsafe, L)
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
                assert (
                    intersection(
                        create_set(seq0.toannotation()), errs0.toassert()
                    ).is_empty()
                ), "Initial sequence contains error states"

        # now we do not support empty sequences
        assert all(map(lambda s: s is not None, seqs0)), "A sequence is none"

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
                        assert is_seq_inductive(tmp, self, L), f"Extended sequence is not inductive)"

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

    def is_loop_header(self, loc):
        return loc in self.get_loop_headers()

    def check(self, onlyedges=None):
        # the initial error path that we check
        loc = self.location
        em = getGlobalExprManager()
        notA = self.assertion.assume_not(em)
        for edge in onlyedges if onlyedges else loc.predecessors():
            state = self.ind_executor().createCleanState()
            state.apply_postcondition(notA)
            self.queue_state(BSEContext(edge, state))

        opt_fold_loops = self.getOptions().fold_loops
        while True:
            bsectx = self.get_next_state()
            if bsectx is None:
                return (
                    Result.UNKNOWN if (self.problematic_states) else Result.SAFE
                ), self.problematic_paths_as_result()

            #ldbgv("Main loop state: {0}", (bsectx,))
            r, pre = self.precondition(bsectx)
            if r is Result.SAFE:
                assert pre is None, "Feasible precondition for infeasible error path"
                continue # infeasible path
            elif r is Result.UNSAFE: # real error
                return r, pre
            else:  #  the error path is feasible, but the errors may not be real
                assert r is Result.UNKNOWN
                if opt_fold_loops:
                    # is this a path starting at a loop header?
                    fl = bsectx.edge.source()
                    if fl not in self.no_sum_loops and self.is_loop_header(fl):
                        if self.handle_loop(fl, pre):
                            dbg(f"Path with loop {fl} proved safe", color="dark_green")
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
                print_stdout(str(states), color="wine")
                print_stdout("Error found.", color="redul")
                self.stats.errors += 1
                return result
            elif result is Result.SAFE:
                print_stdout(
                    f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                )
            elif result is Result.UNKNOWN:
                print_stdout(f"Checking {A} at {loc} was unsuccessful.", color="yellow")
                has_unknown = True
                assert checker.problematic_states, "Unknown with no problematic paths?"
                for p in checker.problematic_states:
                    self.stats.killed_paths += 1
                    report_state(self.stats, p)

        if has_unknown:
            print_stdout("Failed deciding the result.", color="orangeul")
            return Result.UNKNOWN

        print_stdout("No error found.", color="greenul")
        return Result.SAFE
