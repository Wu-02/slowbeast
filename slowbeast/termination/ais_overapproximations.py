from slowbeast.bse.bselfchecker import _check_set_is_inductive_towards
from slowbeast.cfkind.overapproximations import LoopStateOverapproximation
from slowbeast.cfkind.relations import get_const_cmp_relations, get_var_relations
from slowbeast.symexe.statesset import intersection, StatesSet
from slowbeast.util.debugging import dbg, ldbg


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
    overapprox = LoopStateOverapproximation(S, executor, target, unsafe, L, expr_mgr)
    # overapprox.drop_disjuncts()
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
