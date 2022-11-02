from typing import Union

from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.expr import Expr
from slowbeast.domains.exprmgr import ExpressionManager
from slowbeast.solvers.symcrete import global_expr_mgr
from slowbeast.symexe.annotations import (
    ExprAnnotation,
    AssertAnnotation,
    AssumeAnnotation,
)
from slowbeast.symexe.constraints import ConstraintsSet
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.statedescription import (
    StateDescription,
    state_to_description,
    unify_state_descriptions,
    eval_state_description,
)


class StatesSet:
    """
    A symbolic execution state represents a set of concrete states.
    This class is a wrapper that makes it convenient to treat
    SE state as a set of concrete states (i.e., it allows to
    use set operations, etc.

    NOTE that the state given to ctor is stored as a reference,
    i.e. the operations modify the state and it is intentional.
    To avoid this, pass a fresh copy of the state into the ctor
    (state.copy()).

    NOTE 2: the operations do not consider the contents of memory.
    If that is needed, it must be encoded into path-condition and/or
    added as an explicit load annotations.
    """

    __slots__ = "_state"

    def __init__(self, state: SEState) -> None:
        """Create new states set from the given states"""

        assert state is not None and isinstance(state, SEState)
        # assert state.is_feasible(), "Infeasible state given"
        # NOTE: we want to be able to create infeasible states
        # (empty sets)
        self._state = state

    def copy(self) -> "StatesSet":
        return StatesSet(self.get_se_state().copy())

    def expr_manager(self) -> ExpressionManager:
        return global_expr_mgr()

    def get_se_state(self) -> SEState:
        return self._state

    def as_description(self) -> StateDescription:
        return state_to_description(self.get_se_state())

    def as_expr(self):
        """NOTE: use carefully, only when you know what you do..."""
        return self._state.constraints_obj().as_formula(self.expr_manager())

    def as_cnf_expr(self):
        return self.as_expr().to_cnf()

    def rewrite_and_simplify(self) -> "StatesSet":
        self.reset_expr(self.as_expr().rewrite_and_simplify())
        return self

    def as_assume_annotation(self) -> AssumeAnnotation:
        sd = state_to_description(self._state)
        return AssumeAnnotation(
            sd.expr(), sd.substitutions(), self._state.expr_manager()
        )

    def as_assert_annotation(self) -> AssertAnnotation:
        sd = state_to_description(self._state)
        return AssertAnnotation(
            sd.expr(), sd.substitutions(), self._state.expr_manager()
        )

    def reset_expr(self, expr=None) -> "StatesSet":
        """NOTE: use carefully, only when you know what you do..."""
        C = ConstraintsSet()
        if expr is not None:
            C.add(expr)
        self._state.set_constraints(C)
        return self

    def _unite(
        self,
        s: Union[
            ConcreteVal, Expr, ExprAnnotation, SEState, StateDescription, "StatesSet"
        ],
    ) -> None:
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)

        if not state.constraints():
            # the state is clean, just add the first constraints
            state.add_constraint(expr)
            return

        EM = state.expr_manager()
        C = ConstraintsSet()
        newexpr = EM.Or(expr, state.constraints_obj().as_formula(EM))
        if not newexpr.is_concrete():
            C.add(newexpr)
        # else:
        #    # if newexpr is concrete, it must be True. And adding True is useless,
        #    # its the same as empty constraints
        #    assert newexpr.value() is True  # this is Or expr...
        state.set_constraints(C)

    def model(self):
        return self._state.model()

    def unite(self, *S) -> "StatesSet":
        for s in S:
            self._unite(s)
        return self

    def add(self, *S) -> "StatesSet":
        return self.unite(S)

    def intersect(
        self,
        s: Union[
            ConcreteVal, Expr, ExprAnnotation, SEState, StateDescription, "StatesSet"
        ],
    ) -> "StatesSet":
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)
        state.add_constraint(expr)
        return self

    def translate(self, S: SEState) -> "StatesSet":
        """
        Make the set use internally the same variables as 'S'
        """
        selfsd = state_to_description(self._state)

        if isinstance(S, SEState):
            state = S.copy()
        else:
            state = S._state.copy()
        self._state = state
        newexpr = eval_state_description(state.executor(), state, selfsd)
        state.set_constraints(ConstraintsSet((newexpr,)))
        return self

    def translated(self, S: SEState) -> "StatesSet":
        """
        Make the set use internally the same variables as 'S'
        """
        selfsd = state_to_description(self._state)
        if isinstance(S, SEState):
            state = S.copy()
        else:
            state = S._state.copy()
        newexpr = eval_state_description(state.executor(), state, selfsd)
        state.set_constraints(ConstraintsSet((newexpr,)))
        return StatesSet(state)

    def complement(self) -> "StatesSet":
        state = self._state
        EM = state.expr_manager()
        expr = EM.Not(state.constraints_obj().as_formula(EM))
        C = ConstraintsSet()
        C.add(expr)
        state.set_constraints(C)
        return self

    def minus(
        self,
        s: Union[
            ConcreteVal, Expr, ExprAnnotation, SEState, StateDescription, "StatesSet"
        ],
    ) -> "StatesSet":
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.executor(), state, sd)
        EM = state.expr_manager()
        state.add_constraint(EM.Not(expr))
        return self

    def is_empty(self) -> bool:
        """Check whether the set is empty. Involves a solver call"""
        return not self._state.is_feasible()

    def contains(self, S) -> bool:
        X = self.copy()
        X.complement()
        X.intersect(S)
        return X.is_empty()

    def contains_any(self, *Ss) -> bool:
        X = self.copy()
        X.complement()
        for s in Ss:
            if intersection(X, s).is_empty():
                return True
        return False

    def __repr__(self) -> str:
        return f"{{{self.as_description().__repr__()}}}"

    def dump(self) -> None:
        print(f"StateSet{{{self.as_description().__repr__()}}}")


def to_states_descr(
    S: Union[ConcreteVal, Expr, ExprAnnotation, SEState, StateDescription, StatesSet]
) -> StateDescription:
    EM = global_expr_mgr()

    if isinstance(S, StatesSet):
        return S.as_description()
    if isinstance(S, SEState):
        return state_to_description(S)
    elif isinstance(S, StateDescription):
        return S
    elif isinstance(S, ExprAnnotation):
        return S.descr()
    elif isinstance(S, Expr):
        # NOTE: maybe we should have a special method for Expr,
        # because Expr does not fully describe the state (unlike the others)
        # and therefore can break things... For this reason, it would
        # be reasonable to have explicit method conserning adding Expr
        # so that the user is aware of this problem...
        return StateDescription(S, {})
    elif isinstance(S, ConcreteVal) and S.is_bool():
        return StateDescription(S, {})
    elif hasattr(S, "__iter__"):
        R = None
        for s in S:
            if R is None:
                R = to_states_descr(s)
            else:
                expr1, expr2, subs = unify_state_descriptions(EM, R, to_states_descr(s))
                R = StateDescription(EM.Or(expr1, expr2), subs)
        return R

    raise NotImplementedError(f"Unhandled states representation: {type(S)}")


def union(S1: StatesSet, *Ss) -> StatesSet:
    assert isinstance(S1, StatesSet), S1
    X = S1.copy()
    for S in Ss:
        X.add(S)
    return X


def intersection(S1: StatesSet, *Ss) -> StatesSet:
    assert isinstance(S1, StatesSet), S1
    X = S1.copy()
    for S in Ss:
        X.intersect(S)
    return X


def complement(S: StatesSet) -> StatesSet:
    assert isinstance(S, StatesSet), S
    X = S.copy()
    X.complement()
    return X
