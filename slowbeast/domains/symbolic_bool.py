from typing import Optional

from z3 import (
    Bool,
    And,
    Or,
    If,
    Xor,
    Not,
)

from slowbeast.domains.expr import Expr
from slowbeast.domains.symbolic_helpers import (
    TRUE,
    FALSE,
    bv_const,
)
from slowbeast.domains.symbolic_z3 import Z3SymbolicDomain
from slowbeast.domains.value import Value
from slowbeast.ir.types import BoolType, Type, BitVecType


class SymbolicDomainBools(Z3SymbolicDomain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    ##
    # variables
    @staticmethod
    def get_value(name: str, ty: Type) -> Expr:
        assert ty.is_bool()
        return Expr(Bool(name), ty)

    @staticmethod
    def And(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        assert a.is_bool() and b.is_bool()
        return Expr(And(a.unwrap(), b.unwrap()), BoolType())

    @staticmethod
    def Or(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        assert a.is_bool() and b.is_bool()
        return Expr(Or(a.unwrap(), b.unwrap()), BoolType())

    @staticmethod
    def Xor(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        assert a.is_bool() and b.is_bool()
        return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())

    @staticmethod
    def Not(a: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert a.is_bool()
        return Expr(Not(a.unwrap()), BoolType())

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Expr]:
        """Static cast"""
        assert isinstance(a, Expr), a
        tybw = ty.bitwidth()
        if ty.is_bv():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), BitVecType(tybw)
            )
        return None  # unsupported conversion

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert isinstance(a, Expr), a
        tybw = ty.bitwidth()
        if ty.is_bv():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), BitVecType(tybw)
            )

        return None  # unsupported conversion

    @staticmethod
    def get_true() -> Expr:
        return Expr(TRUE(), BoolType())

    @staticmethod
    def get_false() -> Expr:
        return Expr(FALSE(), BoolType())

    @staticmethod
    def Eq(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a} != {b}"
        assert a.is_bool() and b.is_bool()
        return Expr(a == b, BoolType())

    @staticmethod
    def Ne(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bool() and b.is_bool()
        return Expr(a != b, BoolType())
