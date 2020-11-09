from slowbeast.symexe.statedescription import (
    StateDescription,
    state_to_description,
    unify_state_descriptions,
    eval_state_description,
)
from slowbeast.symexe.constraints import ConstraintsSet
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.annotations import (
    ExprAnnotation,
    AssertAnnotation,
    AssumeAnnotation,
)
from slowbeast.domains.symbolic import Expr
from slowbeast.ir.value import Constant

from slowbeast.solvers.solver import getGlobalExprManager


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
    """

    __slots__ = ["_state"]

    def __init__(self, state: SEState):
        """ Create new states set from the given states """

        assert state is not None and isinstance(state, SEState)
        # assert state.isfeasible(), "Infeasible state given"
        # NOTE: we want to be able to create infeasible states
        # (empty sets)
        self._state = state

    def copy(self):
        return StatesSet(self.get_se_state().copy())

    def getExprManager(self):
        return getGlobalExprManager()

    def get_se_state(self):
        return self._state

    def as_description(self):
        return state_to_description(self.get_se_state())

    def as_expr(self):
        """ NOTE: use carefully, only when you know what you do... """
        return self._state.getConstraintsObj().asFormula(self.getExprManager())

    def as_assume_annotation(self):
        sd = state_to_description(self._state)
        return AssumeAnnotation(
            sd.getExpr(), sd.getSubstitutions(), self._state.getExprManager()
        )

    def as_assert_annotation(self):
        sd = state_to_description(self._state)
        return AssertAnnotation(
            sd.getExpr(), sd.getSubstitutions(), self._state.getExprManager()
        )

    def reset_expr(self, expr):
        """ NOTE: use carefully, only when you know what you do... """
        C = ConstraintsSet()
        C.addConstraint(expr)
        self._state.setConstraints(C)

    def _unite(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.getExecutor(), state, sd)

        if not state.getConstraints():
            # the state is clean, just add the first constraints
            state.addConstraint(expr)
            return

        EM = state.getExprManager()
        C = ConstraintsSet()
        newexpr = EM.Or(expr, state.getConstraintsObj().asFormula(EM))
        if not newexpr.is_concrete():
            C.addConstraint(newexpr)
        else:
            # if newexpr is concrete, it must be True. And adding True is useless,
            # its the same as empty constraints
            assert newexpr.value() is True  # this is Or expr...
        state.setConstraints(C)

    def unite(self, *S):
        for s in S:
            self._unite(s)

    def add(self, *S):
        self.unite(S)

    def intersect(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.getExecutor(), state, sd)
        state.addConstraint(expr)

    def complement(self):
        state = self._state
        EM = state.getExprManager()
        expr = EM.Not(state.getConstraintsObj().asFormula(EM))
        C = ConstraintsSet()
        C.addConstraint(expr)
        state.setConstraints(C)

    def minus(self, s):
        state = self._state
        sd = to_states_descr(s)
        expr = eval_state_description(state.getExecutor(), state, sd)
        EM = state.getExprManager()
        state.addConstraint(EM.Not(expr))

    def is_empty(self):
        """ Check whether the set is empty. Involves a solver call """
        return not self._state.isfeasible()

    def __repr__(self):
        return f"{{{self.as_description().__repr__()}}}"

    def dump(self):
        print(f"StateSet{{{self.as_description().__repr__()}}}")


def to_states_descr(S) -> StateDescription:
    EM = getGlobalExprManager()

    if isinstance(S, StatesSet):
        return S.as_description()
    if isinstance(S, SEState):
        return state_to_description(S)
    elif isinstance(S, StateDescription):
        return S
    elif isinstance(S, ExprAnnotation):
        return S.getDescr()
    elif isinstance(S, Expr):
        # NOTE: maybe we should have a special method for Expr,
        # because Expr does not fully describe the state (unlike the others)
        # and therefore can break things... For this reason, it would
        # be reasonable to have explicit method conserning adding Expr
        # so that the user is aware of this problem...
        return StateDescription(S, {})
    elif isinstance(S, Constant) and S.is_bool():
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


def union(S1, *Ss) -> StatesSet:
    X = S1.copy()
    for S in Ss:
        X.add(S)
    return X


def intersection(S1, *Ss) -> StatesSet:
    X = S1.copy()
    for S in Ss:
        X.intersect(S)
    return X


def complement(S) -> StatesSet:
    X = S.copy()
    X.complement()
    return X


#
# class StatesSet:
#     """
#     A unified way how to represent a set of states in symbolic execution.
#     Once we have a StateSet, we can unify or intersect it with other StatesSet,
#     Annotation (StateDescription) or symbolic execution state or with just
#     a formula.
#     """
#     __slots__ = ["_descr"]
#
#     def __init__(self, s):
#         self._descr = none
#         self.add(s)
#
#     def getexprmanager(self):
#         return getglobalexprmanager()
#
#     def get_descr(self):
#         return self._descr
#
#     def _adjoin(self, s, op):
#         em = self.getexprmanager()
#         d = to_states_descr(s)
#         descr = self._descr
#         if descr:
#             e1, e2, subs = unify_state_descriptions(em, d, descr)
#             self._descr = statedescription(op(e1, e2), subs)
#         else:
#             self._descr = d
#
#     def add(self, S):
#         self._adjoin(S, self.getExprManager().Or)
#
#     def intersect(self, S):
#         self._adjoin(S, self.getExprManager().And)
#
#     def union(self, S):
#         self.add(S)
#
#     def negate(self):
#         """ Complement this set in-place """
#         descr = self._descr
#         if descr:
#             descr.setExpr(self.getExprManager().Not(descr.getExpr()))
#
#     def complement(self):
#         """ Returns the complement of this set without modifying it """
#         d = self._descr
#         if d:
#             EM = self.getExprManager()
#             return StatesSet(StateDescription(EM.Not(d), d.getSubstitutions()))
#         return StatesSet()
#
#     def __repr__(self):
#         d = self._descr
#         if d is None:
#             return "{empty}"
#         return f"{{{d.cannonical(self.getExprManager())}}}"
#
#     def dump(self):
#         d = self._descr
#         if d is None:
#             print("{empty}")
#             return
#         print("StatesSet -->:")
#         print(f"Expr:\n{{{d}}}\n")
#         print(f"Cannonical:\n{{{d.cannonical(self.getExprManager())}}}")
#         print("<--:")
#
#
# def to_states_descr(S) -> StateDescription:
#     EM = getGlobalExprManager()
#
#     if isinstance(S, StatesSet):
#         return S.get_descr()
#     if isinstance(S, SEState):
#         return state_to_description(S)
#     elif isinstance(S, StateDescription):
#         return S
#     elif isinstance(S, ExprAnnotation):
#         return S.getDescr()
#     elif isinstance(S, Expr):
#         return StateDescription(S, {})
#     elif S is None and hasattr(S, "__iter__"):
#         R = None
#         for s in S:
#             if R is None:
#                 R = to_states_descr(s)
#             else:
#                 R = unify_state_descriptions(EM, R, to_states_set(s))
#         return R
#
#     raise NotImplementedError("Unhandled states representation")
