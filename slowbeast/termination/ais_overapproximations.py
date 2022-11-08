from slowbeast.bse.bselfchecker import _check_set_is_inductive_towards
from slowbeast.cfkind.overapproximations import LoopStateOverapproximation
from slowbeast.cfkind.relations import get_const_cmp_relations, get_var_relations
from slowbeast.symexe.annotations import AssertAnnotation
from slowbeast.symexe.statesset import intersection, StatesSet
from slowbeast.util.debugging import dbg, ldbg, dbgv, FIXME


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
        ).is_empty(), f"Added realtion {rel} rendered the set infeasible\n{S}"
        assert intersection(
            assumptions, state_as_set, errset
        ).is_empty(), "Added realtion rendered the set unsafe: {rel}"
        assert not state_as_set.is_empty(), "Infeasible states given to overapproximate"
        yield overapprox_set(
            executor,
            state_as_set,
            errset,
            target,
            assumptions,
            loopinfo,
        )


def get_monotonic_variables(state, solver):
    MV = set()
    memory = state.memory
    expr_mgr = state.expr_manager()
    Not, Eq, Le = expr_mgr.Not, expr_mgr.Eq, expr_mgr.Le
    for iptr, ival in memory.input_reads().items():
        val = memory.get_read(iptr)
        if val is None:
            continue

        ival = ival[0]
        if ival.is_pointer():
            assert val.is_pointer()
            # if segment may have been changed, we're screwed and can do notning
            if solver.is_sat(Not(Eq(val.segment(), ival.seqment()))) is True:
                continue
            ival, val = ival.offset(), val.offset()

        if (
            solver.is_sat(Le(val, ival)) is False
            or solver.is_sat(Le(ival, val)) is False
        ):
            MV.add(iptr)

    return MV


class AisLoopStateOverapproximation(LoopStateOverapproximation):
    def drop_clause(self, clause, clauses, assumptions):
        newclauses = super().drop_clause(clause, clauses, assumptions)
        if len(newclauses) == len(clauses):
            assert newclauses is clauses
            # we did nothing
            return newclauses

        # Check that we can find a acyclicity prooving function.
        # If not, dropping the clause is not right.
        if self.clauses_are_acyclic(newclauses, assumptions):
            return newclauses
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
        # check that on all paths we monotonically change at least one variable
        # (same on all paths)
        monotonic_variables = None
        for s in ldata.loop_poststates:
            # feasability check
            solver.push()
            pathcond = substitute(s.path_condition(), (placeholder, lit))
            solver.add(pathcond)
            feasible = solver.try_is_sat(500)
            if feasible is not True:
                solver.pop()
                if feasible is None:  # solver t-outed/failed
                    dbg("Solver failure/timeout")
                    return False
                continue
            # feasible means ok, but we want at least one feasible path
            if monotonic_variables is None:
                monotonic_variables = get_monotonic_variables(s, solver)
            else:
                tmp = get_monotonic_variables(s, solver)
                monotonic_variables.intersection_update(tmp)
            if not monotonic_variables:
                dbg("No monotonically changing variable found")
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

    assert intersection(
        goal, unsafe
    ).is_empty(), f"The goal and unsafe states (the target) overlap"

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
