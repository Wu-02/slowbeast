from typing import Optional

from z3 import And, Or, If, BoolVal, FPVal, Bool, FP, is_bool

from slowbeast.domains.symbolic_helpers import (
    TRUE,
    FALSE,
    bv,
)
from slowbeast.ir.types import type_mgr, Type
from .expr import Expr
from .symbolic_bool import SymbolicDomainBools
from .symbolic_bv import BVSymbolicDomain
from .symbolic_floats import SymbolicDomainFloats
from .symbolic_helpers import get_fp_sort, bv_const
from .symbolic_z3 import Z3SymbolicDomain
from .value import Value


def get_any_domain(a: Expr):
    if a.is_bv():
        return BVSymbolicDomain
    if a.is_bool():
        return SymbolicDomainBools
    if a.is_float():
        return SymbolicDomainFloats
    if a.is_bytes():
        return BVSymbolicDomain
    raise NotImplementedError(f"Unknown domain for value: {a}")


def get_any_domain_checked(a: Value, b: Value):
    assert isinstance(a, Expr), a
    assert isinstance(b, Expr), b
    assert a.type() == b.type(), f"{a.type()} != {b.type()}"
    assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"

    if a.is_bv():
        return BVSymbolicDomain
    if a.is_bool():
        return SymbolicDomainBools
    if a.is_float():
        return SymbolicDomainFloats
    if a.is_bytes():
        return BVSymbolicDomain
    raise NotImplementedError(f"Unknown domain for value: {a}")


def get_bool_or_bv_domain(a: Expr):
    if a.is_bv():
        return BVSymbolicDomain
    if a.is_bool():
        return SymbolicDomainBools
    if a.is_bytes():
        return BVSymbolicDomain
    raise NotImplementedError(f"Unknown domain for value: {a}")


def get_bool_or_bv_domain_checked(a: Value, b: Value):
    assert isinstance(a, Expr), a
    assert isinstance(b, Expr), b
    assert a.type() == b.type(), f"{a.type()} != {b.type()}"
    assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"

    if a.is_bv():
        return BVSymbolicDomain
    if a.is_bool():
        return SymbolicDomainBools
    if a.is_bytes():
        return BVSymbolicDomain
    raise NotImplementedError(f"Unknown domain for value: {a}")


class SymbolicDomain(Z3SymbolicDomain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    @staticmethod
    def lift(v: Value) -> Expr:
        assert isinstance(v, Value), f"Invalid value for lifting: {v}"
        if isinstance(v, Expr):
            return v

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), type_mgr().bool_ty())
            ty = v.type()
            if v.is_float():
                return Expr(FPVal(float(v.value()), get_fp_sort(ty.bitwidth())), ty)
            return Expr(bv_const(v.value(), ty.bitwidth()), ty)

        raise NotImplementedError(f"Invalid value for lifting: {v}")

    ##
    # variables
    @staticmethod
    def get_value(name: str, ty: Type) -> Expr:
        if ty.is_float():
            return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)
        elif ty.is_bool():
            return Expr(Bool(name), ty)
        else:
            assert ty.is_bv() or ty.is_pointer(), ty
            return Expr(bv(name, ty.bitwidth()), ty)

    ##
    # Logic operators
    @staticmethod
    def conjunction(*args) -> Expr:
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert all((isinstance(a, Expr) for a in args))
        assert all((a.is_bool() for a in args))
        assert all((is_bool(a.unwrap()) for a in args))
        return Expr(And(*(x.unwrap() for x in args)), type_mgr().bool_ty())

    @staticmethod
    def disjunction(*args) -> Expr:
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert all((isinstance(a, Expr) for a in args))
        assert all((a.is_bool() for a in args))
        assert all((is_bool(a.unwrap()) for a in args))
        return Expr(Or(*(x.unwrap() for x in args)), type_mgr().bool_ty())

    @staticmethod
    def Ite(c: Expr, a, b) -> Expr:
        assert isinstance(c, Expr), c
        assert c.is_bool(), c
        assert is_bool(c.unwrap()), c
        assert a.type() == b.type(), f"{a}, {b}"
        return Expr(If(c.unwrap(), a.unwrap(), b.unwrap()), a.type())

    @staticmethod
    def And(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).And(a, b)

    @staticmethod
    def Or(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).Or(a, b)

    @staticmethod
    def Xor(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).Xor(a, b)

    @staticmethod
    def Not(a: Expr) -> Expr:
        assert isinstance(a, Expr), a
        return get_bool_or_bv_domain(a).Not(a)

    @staticmethod
    def Extend(a: Value, bw: int, unsigned: bool) -> Expr:
        return BVSymbolicDomain.Extend(a, bw, unsigned)

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Expr]:
        """Static cast"""
        assert isinstance(a, Expr), a
        return get_any_domain(a).BitCast(a, ty)

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert isinstance(a, Expr), a
        return get_any_domain(a).Cast(a, ty, signed)

    @staticmethod
    def Extract(a: Expr, start: int, end: int) -> Expr:
        return BVSymbolicDomain.Extract(a, start, end)

    @staticmethod
    def Concat(*args):
        return BVSymbolicDomain.Concat(*args)

    @staticmethod
    def Shl(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return BVSymbolicDomain.Shl(a, b)

    @staticmethod
    def AShr(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return BVSymbolicDomain.AShr(a, b)

    @staticmethod
    def LShr(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return BVSymbolicDomain.LShr(a, b)

    @staticmethod
    def get_true() -> Expr:
        return Expr(TRUE(), type_mgr().bool_ty())

    @staticmethod
    def get_false() -> Expr:
        return Expr(FALSE(), type_mgr().bool_ty())

    ### Relational operators
    @staticmethod
    def Le(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        return get_any_domain_checked(a, b).Le(a, b, unsigned)

    @staticmethod
    def Lt(a, b, unsigned: bool = False) -> Expr:
        return get_any_domain_checked(a, b).Lt(a, b, unsigned)

    @staticmethod
    def Ge(a, b, unsigned: bool = False) -> Expr:
        return get_any_domain_checked(a, b).Ge(a, b, unsigned)

    @staticmethod
    def Gt(a, b, unsigned: bool = False) -> Expr:
        return get_any_domain_checked(a, b).Gt(a, b, unsigned)

    @staticmethod
    def Eq(a, b) -> Expr:
        return get_any_domain_checked(a, b).Eq(a, b)

    @staticmethod
    def Ne(a, b) -> Expr:
        return get_any_domain_checked(a, b).Ne(a, b)

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).Add(a, b)

    @staticmethod
    def Sub(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).Sub(a, b)

    @staticmethod
    def Mul(a: Expr, b: Expr) -> Expr:
        return get_any_domain_checked(a, b).Mul(a, b)

    def Div(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        return get_any_domain_checked(a, b).Div(a, b, unsigned)

    @staticmethod
    def Rem(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        return BVSymbolicDomain.Rem(a, b, unsigned)

    @staticmethod
    def Abs(a: Expr) -> Expr:
        return get_any_domain(a).Abs(a)

    @staticmethod
    def Neg(a: Expr) -> Expr:
        """Return the negated number"""
        return get_any_domain(a).Neg(a)

    @staticmethod
    def FpOp(op, val) -> Optional[Expr]:
        return SymbolicDomainFloats.FpOp(op, val)
