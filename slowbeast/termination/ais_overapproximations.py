from slowbeast.bse.bse import check_paths
from slowbeast.bse.bselfchecker import _check_set_is_inductive_towards
from slowbeast.cfkind.overapproximations import LoopStateOverapproximation
from slowbeast.cfkind.relations import get_const_cmp_relations, get_var_relations
from slowbeast.solvers.symcrete import IncrementalSolver
from slowbeast.symexe.annotations import AssertAnnotation
from slowbeast.symexe.statesset import intersection, StatesSet, union
from slowbeast.util.debugging import dbg, ldbg, FIXME, dbgv

from itertools import permutations


def overapprox_state(executor, state_as_set, errset: StatesSet, target, loopinfo):
    if not _check_set_is_inductive_towards(executor, state_as_set, loopinfo, target):
        return

    # add relations
    for rel in get_const_cmp_relations(state_as_set.get_se_state()):
        ldbg("  Adding relation {0}", (rel,))

        state_as_set.intersect(rel)
        assert (
            not state_as_set.is_empty()
        ), f"Added realtion {rel} rendered the set infeasible\n{state_as_set}"
        assert intersection(
            state_as_set, errset
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"

    yield from _overapprox_with_assumptions(
        errset, loopinfo, state_as_set, executor, target
    )

    # try without any relation
    # assert not S.is_empty(), "Infeasible states given to overapproximate"
    yield overapprox_set(executor, state_as_set, errset, target, None, loopinfo)


def _overapprox_with_assumptions(errset, loopinfo, state_as_set, executor, target):
    """
    Infer a set of relations that hold in S and over-approximate the set
    w.r.t. these relations.
    """
    # precise prestates of this state
    relations = set(get_var_relations([state_as_set.get_se_state()], prevsafe=target))
    if not relations:
        return
    yield from _yield_overapprox_with_assumption(
        errset, loopinfo, state_as_set, executor, relations, target
    )


def _yield_overapprox_with_assumption(
    errset, loopinfo, state_as_set, executor, rels, target
):
    create_set = executor.create_set
    for rel in rels:
        ldbg("  Using assumption {0}", (rel,))
        assumptions = create_set(rel)
        assert not intersection(
            assumptions, state_as_set
        ).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{target}"
        assert intersection(
            assumptions, state_as_set, errset
        ).is_empty(), f"Added realtion rendered the set unsafe: {rel} ;; {errset}"
        assert not state_as_set.is_empty(), "Infeasible states given to overapproximate"
        yield overapprox_set(
            executor,
            state_as_set,
            errset,
            target,
            assumptions,
            loopinfo,
        )


def get_changing_variables(state, solver):
    nonincV, decV = set(), set()
    nondecV, incV = set(), set()
    memory = state.memory
    expr_mgr = state.expr_manager()
    Not, Eq, Le, Lt = expr_mgr.Not, expr_mgr.Eq, expr_mgr.Le, expr_mgr.Lt
    for iptr, ival in memory.input_reads().items():
        val = memory.get_read(iptr)
        if val is None:
            # the memory was not modified on this path,
            # add it to non-decreasing and non-increasing sets
            nondecV.add(iptr)
            nonincV.add(iptr)
            continue

        ival = ival[0]
        if ival.is_pointer():
            assert val.is_pointer()
            # if object may have been changed, we're screwed and can do notning
            if solver.is_sat(Not(Eq(val.object(), ival.object()))) is True:
                continue
            ival, val = ival.offset(), val.offset()

        if solver.is_sat(Lt(val, ival)) is False:  # val >= ival
            if solver.is_sat(Le(val, ival)) is False:  # val > ival
                incV.add(iptr)
            else:
                nondecV.add(iptr)
        if solver.is_sat(Lt(ival, val)) is False:  # val <= ival
            if solver.is_sat(Le(ival, val)) is False:  # val < ival
                decV.add(iptr)
            else:
                nonincV.add(iptr)

    return decV, incV, nondecV, nonincV


def get_lexicographic_orderings(decV, nonincV):
    # FIXME: do this more efficiently
    return {
        prefix + suffix
        for prefix in permutations(nonincV)
        for suffix in permutations(decV)
    }


def _is_good_ord(ord, decV, nonincV):
    for var in ord:
        if var not in nonincV:
            if var in decV:  # we're fine
                return True
            else:
                return False
        if var in decV:  # this is redundant if the sets are disjoint...
            return True
    return False


def update_lex_orderings(ords, decV, nonincV):
    return {ord for ord in ords if _is_good_ord(ord, decV, nonincV)}


class AisLoopStateOverapproximation(LoopStateOverapproximation):
    def drop_clause(self, clause, clauses, assumptions):
        """
        Try dropping the clause. If successful, return a list of new clauses.
        DO NOT modify 'clauses' parameter!.
        """
        assert not clause.is_concrete(), clause
        # create a temporary formula without the given clause
        tmpclauses = clauses.copy()
        tmpclauses.remove(clause)

        # check whether we can get rid of the clause
        if assumptions:
            tmpexpr = self.expr_mgr.conjunction(*tmpclauses, assumptions.as_expr())
        else:
            tmpexpr = self.expr_mgr.conjunction(*tmpclauses)
        if tmpexpr.is_concrete():
            return (
                clauses  # either False or True are bad for us, return original clauses
            )

        # == safety check
        if self.safesolver.is_sat(tmpexpr) is not False:
            return clauses  # unsafe overapprox, do not drop

        # == feasability, acyclicity and inductiveness check
        pre = self.goal.copy()
        pre.reset_expr(tmpexpr)
        # if self.loop.set_is_inductive_towards(X, self.target):
        #    dbg(f"  dropped {clause}...")
        #    return tmpclauses
        # inc_variables, dec_variables = None, None
        lex_dec, lex_inc = None, None
        executor = self.executor
        post = union(pre, self.target)
        have_feasible = False
        solver = IncrementalSolver()
        for path in self.loop.paths():
            p = path.copy()
            if post:
                p.add_annot_after(post.as_assert_annotation())
            if pre:
                p.add_annot_before(pre.as_assume_annotation())

            r = executor.execute_path(p)
            if r.errors:  # not inductive
                return clauses

            if not r.ready:
                continue

            have_feasible = True

            # check acyclicity
            for s in r.ready:
                solver.push()
                solver.add(s.path_condition())
                decV, incV, nondecV, nonincV = get_changing_variables(s, solver)
                solver.pop()

                # if inc_variables is None:
                #    inc_variables = incV
                # else:
                #    inc_variables.intersection_update(incV)

                # if dec_variables is None:
                #    dec_variables = decV
                # else:
                #    dec_variables.intersection_update(decV)

                if not (decV or incV):
                    # no variable strictly changes on this path, we're done
                    return clauses

                if lex_dec is None:
                    lex_dec = get_lexicographic_orderings(decV, nonincV)
                else:
                    lex_dec = update_lex_orderings(lex_dec, decV, nonincV)

                if lex_inc is None:
                    lex_inc = get_lexicographic_orderings(incV, nondecV)
                else:
                    lex_inc = update_lex_orderings(lex_inc, incV, nondecV)

                # if not (inc_variables or dec_variables) and not (lex_inc or lex_dec):
                if not (lex_inc or lex_dec):
                    dbgv("No monotonicity or lexicographic argument for progress found")
                    return clauses

        if have_feasible:
            dbg(f"  dropped {clause}...")
            return tmpclauses
        return clauses

    def check_literal(self, lit, ldata) -> bool:
        """
        Check that replacit literal in ldata with `lit` gives us a valid AIS
        """
        if lit is None or lit.is_concrete():
            return False

        expr_mgr = self.expr_mgr
        # safety check
        if (
            not ldata.safety_solver.try_is_sat(
                500, expr_mgr.disjunction(lit, *ldata.clause)
            )
            is False
        ):
            return False

        have_feasible = False
        substitute = expr_mgr.substitute

        I = ldata.indset_with_placeholder
        placeholder = ldata.placeholder
        solver = ldata.solver
        A = AssertAnnotation(
            substitute(I.expr(), (placeholder, lit)), I.substitutions(), expr_mgr
        )
        # check that on all paths we strictly change at least one variable
        # (same on all paths and in the same direction), i.e., it must hold
        # for some variable a that (forall p: a' < a) or (forall p: a' > a)
        # inc_variables, dec_variables = None, None
        lex_dec, lex_inc = None, None
        for s in ldata.loop_poststates:
            # -- feasability check
            solver.push()
            pathcond = substitute(s.path_condition(), (placeholder, lit))
            solver.add(pathcond)
            feasible = solver.try_is_sat(1000)
            if feasible is not True:
                solver.pop()
                if feasible is None:  # solver t-outed/failed
                    dbg("Solver failure/timeout")
                    return False
                continue

            # we found at least one feasible path, good
            # now check if we find some strictly changing variables
            # or some lexicographic argument that ensures progress
            decV, incV, nondecV, nonincV = get_changing_variables(s, solver)
            # if inc_variables is None:
            #    inc_variables = incV
            # else:
            #    inc_variables.intersection_update(incV)

            # if dec_variables is None:
            #    dec_variables = decV
            # else:
            #    dec_variables.intersection_update(decV)

            if not (decV or incV):
                # no variable strictly changes on this path, we're done
                solver.pop()
                return False

            if lex_dec is None:
                lex_dec = get_lexicographic_orderings(decV, nonincV)
            else:
                lex_dec = update_lex_orderings(lex_dec, decV, nonincV)

            if lex_inc is None:
                lex_inc = get_lexicographic_orderings(incV, nondecV)
            else:
                lex_inc = update_lex_orderings(lex_inc, incV, nondecV)

            # if not (inc_variables or dec_variables) and not (lex_inc or lex_dec):
            if not (lex_inc or lex_dec):
                dbgv("No monotonicity or lexicographic argument for progress found")
                solver.pop()
                return False
            have_feasible = True

            # inductivity check
            hasnocti = A.do_substitutions(s)
            # we have got pathcond in solver already
            if (
                solver.try_is_sat(500, expr_mgr.Not(hasnocti)) is not False
            ):  # there exist CTI
                solver.pop()
                return False
            solver.pop()
        return have_feasible  # and change_is_monotonic

    def clauses_are_acyclic(self, clauses, assumptions):
        FIXME("Checking acyclicity in dropping clauses not implemented")
        return False


def overapprox_set(
    executor,
    goal: StatesSet,
    unsafe: StatesSet,
    indtarget,
    assumptions,
    L,
    drop_only: bool = False,
):
    """
    goal - the set to be overapproxiamted
    drop_only - only try to drop clauses, not to extend them
    """
    create_set = executor.create_set
    # unify variables in goal, target, and unsafe
    S = goal.translated(unsafe)
    target = indtarget.translated(unsafe)
    if assumptions:
        assumptions = assumptions.translated(unsafe)

    if __debug__:
        assert L.set_is_inductive_towards(
            S, target, allow_infeasible_only=True
        ), f"{S} -> {target}"

    dbg(f"Overapproximating {S}", color="dark_blue")
    dbg(f"  with target: {target}", color="dark_blue")
    dbg(f"  with unsafe states: {unsafe}", color="dark_blue")
    if assumptions:
        dbg(f"  and assumptions: {assumptions}", color="dark_blue")

    # assert intersection(
    #    goal, unsafe
    # ).is_empty(), f"The goal and unsafe states (the target) overlap"
    if not intersection(goal, unsafe).is_empty():
        dbg(
            f"The goal and unsafe states (the target) overlap. Probably nondet() in loop"
        )
        return None

    expr = S.as_expr()
    if expr.is_concrete():
        return S

    expr_mgr = S.expr_manager()
    overapprox = AisLoopStateOverapproximation(S, executor, target, unsafe, L, expr_mgr)
    overapprox.drop_clauses(assumptions)

    # NOTE: this works good alone sometimes
    if drop_only:
        S = overapprox.commit()
        return S

    overapprox.overapproximate()

    # drop clauses once more
    overapprox.drop_clauses(None)
    S = overapprox.commit()

    assert intersection(
        unsafe, create_set(S)
    ).is_empty(), "Dropping clauses second time made the set unsafe"

    dbg(f"Overapproximated to {S}", color="orange")

    return S
