from slowbeast.domains.symbolic_helpers import map_model
from slowbeast.domains.exprmgr import ExpressionManager
from slowbeast.solvers.solver import SolverIntf
from slowbeast.solvers.z3solver import models, models_inc, _is_sat
from z3 import Solver as Z3Solver, is_false, BoolVal
from slowbeast.domains.concrete_value import ConcreteVal
from typing import List, Optional, Union

global_expr_manager = ExpressionManager()


def global_expr_mgr() -> ExpressionManager:
    global global_expr_manager
    return global_expr_manager


class SymbolicSolver(SolverIntf):
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self) -> None:
        super().__init__(global_expr_mgr())

    def is_sat(self, *e) -> Optional[bool]:
        if any(
            map(lambda x: is_false(x) or (x.is_concrete() and x.value() is False), e)
        ):
            return False
        return _is_sat(
            Z3Solver(), None, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def try_is_sat(self, timeout, *e) -> Optional[bool]:
        if any(
            map(lambda x: is_false(x) or (x.is_concrete() and x.value() is False), e)
        ):
            return False
        return _is_sat(
            Z3Solver(), timeout, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def concretize(self, assumpt, *e) -> Union[None, List[None], List[ConcreteVal]]:
        assert all(
            map(lambda x: not x.is_concrete(), e)
        ), "ConcreteVal instead of symbolic value"
        if any(map(lambda x: x.is_concrete() and x.value() is False, assumpt)):
            return None
        m = models(assumpt, *e)
        return map_model(m, e)


class IncrementalSolver(SymbolicSolver):
    def __init__(self) -> None:
        # FIXME: add local expr manager
        super().__init__()
        self._solver = Z3Solver()

    def add(self, *e) -> None:
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            self._solver.add(BoolVal(False))
        self._solver.add(*(x.unwrap() for x in e if not x.is_concrete()))

    def push(self) -> None:
        self._solver.push()

    def pop(self, num: int = 1) -> None:
        self._solver.pop(num)

    def is_sat(self, *e) -> Optional[bool]:
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return _is_sat(
            self._solver, None, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def try_is_sat(self, timeout, *e) -> Optional[bool]:
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return _is_sat(
            self._solver, timeout, *(x.unwrap() for x in e if not x.is_concrete())
        )

    def copy(self) -> "IncrementalSolver":
        s = IncrementalSolver()
        s._solver = self._solver.translate(self._solver.ctx)
        return s

    def concretize(self, assumpt, *e) -> Union[None, List[None], List[ConcreteVal]]:
        assert all(
            map(lambda x: not x.is_concrete(), e)
        ), "ConcreteVal instead of symbolic value"
        if any(map(lambda x: x.is_concrete() and x.value() is False, assumpt)):
            return None
        m = models_inc(self._solver, assumpt, *e)
        return map_model(m, e)

    def _model(self):
        """Debugging feature atm. Must follow is_sat() that is True"""
        return self._solver.model()

    def __repr__(self) -> str:
        return f"IncrementalSolver: {self._solver}"


def _sort_subs(subs):
    """
    Return multiplication of two variables later than other expressions
    """
    # FIXME: not very efficient
    V = []
    for k, v in subs.items():
        s = sum(map(lambda c: not c.is_concrete(), k.children()))
        if s > 1:
            V.append((k, v))
        else:
            yield (k, v)
    for k, v in V:
        yield (k, v)


def _rewrite_poly(em, exprs, assumptions=None):
    expr = em.conjunction(*exprs)
    if expr.is_concrete():
        return expr
    expr1 = expr.rewrite_polynomials(assumptions)
    if assumptions:
        A = []
        for i in range(len(assumptions)):
            a = assumptions[i]
            A.append(a.rewrite_polynomials(assumptions))
        return em.conjunction(*A, expr1)
    return expr1


def solve_incrementally(assumptions, exprs, em, to1: int = 3000, to2: int = 500):
    # check if we can evaluate some expression syntactically
    for a in assumptions:
        exprs = [em.substitute(e, (a, em.get_true())) for e in exprs]
    # filter out expressions that are 'true'
    exprs = [e for e in exprs if not (e.is_concrete() and bool(e.value()))]

    if assumptions:
        exprs, r = _remove_implied(assumptions, em, exprs)
        if r is not None:
            return r

    # First try to rewrite the formula into a simpler form
    expr = _rewrite_poly(em, exprs, assumptions)
    if expr.is_concrete():
        return bool(expr.value())
    exprcnf = expr.to_cnf()
    eqs = exprcnf.infer_equalities()
    if eqs:
        expr = _rewrite_poly(em, list(exprcnf.children()), eqs)
        if not expr.is_concrete():
            exprs, r = _remove_implied(eqs, em, expr.to_cnf().children())
            if r is not None:
                return r
            expr = em.conjunction(*exprs, *eqs)
    # else: keep the last expr that we had

    if expr.is_concrete():
        return bool(expr.value())

    # FIXME: transfer state from _remove_implied
    solver = IncrementalSolver()

    # FIXME try reduced bitwidth with propagating back models instead of this
    # for bw in (1, 2, 4, 8, 16):
    #    # FIXME: handle signed/unsinged and negations correctly in
    #    # reduce_arith_bitwidth and use that
    #    solver.add(expr.reduce_eq_bitwidth(bw).rewrite_and_simplify())
    #    r = solver.try_is_sat(bw*500)
    #    if r is False: return False
    #    elif r is None:
    #        break
    #    assert r is True
    #    # the reduced subformulas are sat. Try to check the original formula
    #    # with the knowledge about the reduced formulas stored in the solver
    #    r = solver.try_is_sat(bw*500, expr)
    #    if r is not None:
    #        return r
    ###
    # Now try abstractions
    #
    rexpr, subs = expr.replace_arith_ops()
    if rexpr:
        solver.push()
        solver.add(rexpr.rewrite_and_simplify())
        n = 0
        for placeholder, e in _sort_subs(subs):
            n += 1
            if solver.try_is_sat(n * to2) is False:
                return False
            solver.add(em.Eq(e, placeholder))
        solver.pop()
    # fall-back to solving the un-abstracted expression
    return solver.is_sat(expr)


def _remove_implied(assumptions, em, exprs):
    solver = IncrementalSolver()
    solver.add(*assumptions)
    # check the assumpitons - if we are able to check them on their own,
    r = solver.try_is_sat(1000)
    if r is False:
        return [em.get_false()], False
    # we're good and can continue -- the solver has built a state for faster
    # solving now

    # try to subsume the implied expressions
    # assert solver.is_sat() is True # otherwise we'll subsume everything
    exprs = [e for e in exprs if solver.try_is_sat(500, em.Not(e)) is not False]
    r = solver.try_is_sat(1000, *exprs)
    return exprs, r


Solver = SymbolicSolver
