from typing import Union

from z3 import (
    simplify,
    substitute,
)

from slowbeast.domains.concrete import ConcreteDomain
from slowbeast.domains.expr import Expr
from slowbeast.domains.symbolic_helpers import (
    python_constant,
    python_to_sb_type,
)
from .domain import Domain


class Z3SymbolicDomain(Domain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    @staticmethod
    def simplify(expr: Expr) -> Expr:
        return Expr(
            simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.type()
        )

    @staticmethod
    def to_python_constant(expr: Expr):
        return python_constant(expr.unwrap())

    @staticmethod
    def substitute(expr: Expr, *what) -> Union[ConcreteDomain.get_value, Expr]:
        e = simplify(
            substitute(expr.unwrap(), *((a.unwrap(), b.unwrap()) for (a, b) in what))
        )
        c = python_constant(e)
        if c is not None:
            return ConcreteDomain.get_value(
                c, python_to_sb_type(c, expr.type().bitwidth())
            )
        return Expr(e, expr.type())
