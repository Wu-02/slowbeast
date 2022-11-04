from typing import Optional

from z3 import (
    FP,
    And,
    If,
    Not,
    fpFPToFP,
    RNE,
    fpToIEEEBV,
    fpLEQ,
    fpIsNaN,
    fpLT,
    fpGEQ,
    fpGT,
    fpEQ,
    fpNEQ,
    fpDiv,
    fpAbs,
    fpNeg,
    fpIsInf,
    fpIsZero,
    fpIsSubnormal,
    fpIsNegative,
)

from slowbeast.domains.expr import Expr
from slowbeast.domains.symbolic_helpers import (
    get_fp_sort,
    trunc_fp,
    to_double,
    float_to_ubv,
    float_to_sbv,
    bv_const,
    cast_to_fp,
)
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import FpOp
from slowbeast.ir.types import Type, type_mgr
from slowbeast.util.debugging import FIXME
from .symbolic_z3 import Z3SymbolicDomain


def check_args(a, b):
    assert isinstance(a, Expr), a
    assert isinstance(b, Expr), b
    assert a.type() == b.type(), f"{a.type()} != {b.type()}"
    assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
    assert a.is_float(), a


class SymbolicDomainFloats(Z3SymbolicDomain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    ##
    # variables
    @staticmethod
    def get_value(name: str, ty: Type) -> Expr:
        assert ty.is_float(), ty
        return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Expr]:
        """Static cast of float (a) to some type"""
        assert isinstance(a, Expr), a
        assert a.is_float(), a
        tybw = ty.bitwidth()
        if ty.is_float():
            return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        if ty.is_bv():
            ae = fpToIEEEBV(a.unwrap())
            return Expr(ae, ty)
        return None  # unsupported conversion

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert isinstance(a, Expr), a
        assert a.is_float(), a
        tybw = ty.bitwidth()
        if ty.is_float():
            return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        if ty.is_bv():
            if signed:
                ae = float_to_sbv(a, ty)
            else:
                ae = float_to_ubv(a, ty)
            # ae = fpToIEEEBV(a._value)
            return Expr(ae, ty)
        return None  # unsupported conversion

    ### Relational operators
    @staticmethod
    def Le(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        check_args(a, b)
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpLEQ(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    @staticmethod
    def Lt(a, b, unsigned: bool = False) -> Expr:
        check_args(a, b)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpLT(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    @staticmethod
    def Ge(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        check_args(a, b)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpGEQ(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    @staticmethod
    def Gt(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        check_args(a, b)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpGT(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    @staticmethod
    def Eq(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        check_args(a, b)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpEQ(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    @staticmethod
    def Ne(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        check_args(a, b)
        a, b = cast_to_fp(a), cast_to_fp(b)
        expr = fpNEQ(a, b)
        if not unsigned:
            expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
        return Expr(expr, type_mgr().bool_ty())

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Expr, b: Expr) -> Expr:
        check_args(a, b)
        bw = a.bitwidth()
        # the operations on CPU work on doubles( well, 80-bits...)
        # and then truncate to float if needed
        ae = to_double(a)
        be = to_double(b)
        return Expr(trunc_fp(ae + be, bw), type_mgr().float_ty(bw))

    @staticmethod
    def Sub(a: Expr, b: Expr) -> Expr:
        check_args(a, b)
        bw = a.bitwidth()
        ae = to_double(a)
        be = to_double(b)
        return Expr(trunc_fp(ae - be, bw), type_mgr().float_ty(bw))

    @staticmethod
    def Mul(a: Expr, b: Expr) -> Expr:
        check_args(a, b)
        bw = a.bitwidth()
        ae = to_double(a)
        be = to_double(b)
        return Expr(trunc_fp(ae * be, bw), type_mgr().float_ty(bw))

    @staticmethod
    def Div(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        check_args(a, b)
        bw = a.bitwidth()
        ae = to_double(a)
        be = to_double(b)
        return Expr(trunc_fp(fpDiv(RNE(), ae, be), bw), type_mgr().float_ty(bw))

    @staticmethod
    def Abs(a: Expr) -> Expr:
        assert isinstance(a, Expr), a
        return Expr(fpAbs(a.unwrap()), a.type())

    @staticmethod
    def Neg(a: Expr) -> Expr:
        """Return the negated number"""
        assert isinstance(a, Expr), a
        bw = a.bitwidth()
        return Expr(trunc_fp(fpNeg(to_double(a)), bw), type_mgr().float_ty(bw))

    @staticmethod
    def FpOp(op, val) -> Optional[Expr]:
        assert isinstance(val, Expr), val
        # FIXME: do not use the enum from instruction
        assert val.is_float()

        if op == FpOp.IS_INF:
            return Expr(fpIsInf(val.unwrap()), type_mgr().bool_ty())
        if op == FpOp.IS_NAN:
            return Expr(fpIsNaN(val.unwrap()), type_mgr().bool_ty())
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.unwrap()
            expr = If(
                fpIsNaN(v),
                bv_const(0, 32),
                If(
                    fpIsInf(v),
                    bv_const(1, 32),
                    If(
                        fpIsZero(v),
                        bv_const(2, 32),
                        If(fpIsSubnormal(v), bv_const(3, 32), bv_const(4, 32)),
                    ),
                ),
            )
            return Expr(expr, type_mgr().bv_ty(32))
            if op == FpOp.SIGNBIT:
                return Expr(
                    If(fpIsNegative(bv_const(1, 32), bv_const(0, 32))),
                    type_mgr().bv_ty(32),
                )

        return None
