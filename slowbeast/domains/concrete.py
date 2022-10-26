from math import isinf, isnan, isfinite
from struct import pack, unpack
from typing import Optional, Union

from numpy.core import float_

from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.concrete_bool import ConcreteBoolDomain
from slowbeast.domains.concrete_floats import ConcreteFloat, ConcreteFloatsDomain
from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.ir.instruction import FpOp
from slowbeast.ir.types import Type
from slowbeast.util.debugging import FIXME
from .concrete_bitvec import (
    to_bv,
    ConcreteBitVecDomain,
)
from .domain import Domain


def trunc_to_float(x, bw):
    # isnt there a more efficient way? Probably just to use numpy.float32
    # (but it seem to use a different rounding mode), or write the float
    # handling directly in C (there must be a library with Python bindings
    # for that)
    if bw == 32:
        return unpack("f", pack("f", x))[0]
    return x


def to_fp(x, unsigned: bool = False):
    val = x.value()
    if x.is_float():
        return val
    return (
        unpack("f", pack("I", val))
        if x.bitwidth() == 32
        else unpack("d", pack("Q", val))
    )[0]


class ConcreteDomain(Domain):
    """
    Takes care of handling concrete computations.
    """

    @staticmethod
    def Value(c: int, bw: int) -> ConcreteVal:
        if isinstance(c, bool):
            assert bw == 1, bw
            return ConcreteBool(c)
        if isinstance(c, int):
            return ConcreteBitVec(c, bw)
        if isinstance(c, (float, float_)):
            return ConcreteFloat(c, bw)
        raise NotImplementedError(
            "Don't know how to create a ConcretValue for {c}: {type(c)}"
        )

    @staticmethod
    def get_true() -> ConcreteBool:
        return ConcreteBool(True)

    @staticmethod
    def get_false() -> ConcreteBool:
        return ConcreteBool(False)

    @staticmethod
    def conjunction(*args) -> ConcreteBool:
        return ConcreteBoolDomain.conjunction(*args)

    @staticmethod
    def disjunction(*args) -> ConcreteBool:
        return ConcreteBoolDomain.disjunction(*args)

    @staticmethod
    def Ite(c: Value, a: Value, b: Value):
        assert isinstance(c, ConcreteBool), c
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return a if c else b

    @staticmethod
    def And(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.And(a, b)
        elif a.is_bv():
            return ConcreteBitVecDomain.And(a, b)
        raise NotImplementedError(f"Operation not implemented: And({a}, {b})")

    @staticmethod
    def Or(a: ConcreteVal, b: ConcreteVal) -> ConcreteVal:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.Or(a, b)
        elif a.is_bv():
            return ConcreteBitVecDomain.Or(a, b)
        raise NotImplementedError(f"Operation not implemented: Or({a}, {b})")

    @staticmethod
    def Xor(a: ConcreteVal, b: ConcreteVal) -> ConcreteVal:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.Xor(a, b)
        elif a.is_bv():
            return ConcreteBitVec(to_bv(a) ^ to_bv(b), a.bitwidth())
        raise NotImplementedError(f"Operation not implemented: Xor({a}, {b})")

    @staticmethod
    def Not(a: ConcreteVal) -> ConcreteVal:
        assert isinstance(a, ConcreteVal), a
        if a.is_bool():
            return ConcreteBoolDomain.Not(a)
        raise NotImplementedError(f"Operation not implemented: Not({a})")

    @staticmethod
    def Extend(a: ConcreteVal, b: int, unsigned: bool) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, int), b
        assert not a.is_float(), "No extend for floats implemented"
        return ConcreteBitVecDomain.Extend(a, b, unsigned)

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = False) -> Optional[Value]:
        """Reinterpret cast"""

        assert isinstance(a, ConcreteVal), a
        bw = ty.bitwidth()
        if a.is_bool() and ty.is_bv():
            return ConcreteBitVec(1 if a.value() != 0 else 0, bw)
        if a.is_bytes() and ty.is_float():
            return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
        if a.is_bv():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(float(a.value()), bw), bw)
            elif ty.is_bv():
                return ConcreteBitVec(a.value(), bw)
            elif ty.is_bool():
                return ConcreteBool(False if a.value() == 0 else True)
        elif a.is_float():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(a.value(), bw), bw)
            elif ty.is_bv():
                return ConcreteBitVec(int(a.value()), bw)
        return None  # unsupported conversion

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[ConcreteVal]:
        """static cast"""
        assert isinstance(a, ConcreteVal), a
        bw = ty.bitwidth()
        if a.is_bool() and ty.is_bv():
            return ConcreteBitVec(1 if a.value() else 0, bw)
        if a.is_bytes() and ty.is_float():
            return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
        if a.is_bv():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
            elif ty.is_bv():
                return ConcreteBitVec(a.value(), bw)
            elif ty.is_bool():
                return ConcreteBool(False if a.value() == 0 else True)
        elif a.is_float():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(a.value(), bw), bw)
            elif ty.is_bv():
                return ConcreteBitVec(to_bv(a), bw)
        return None  # unsupported conversion

    @staticmethod
    def Shl(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBitVec), a
        return ConcreteBitVecDomain.Shl(a, b)

    @staticmethod
    def AShr(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBitVec), a
        return ConcreteBitVecDomain.AShr(a, b)

    @staticmethod
    def LShr(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBitVec), a
        return ConcreteBitVecDomain.LShr(a, b)

    @staticmethod
    def Extract(a: Value, start: ConcreteVal, end: ConcreteVal) -> Value:
        assert isinstance(a, ConcreteBitVec), a
        return ConcreteBitVecDomain.Extract(a, start, end)

    @staticmethod
    def Concat(*args) -> Value:
        return ConcreteBitVecDomain.Concat(*args)

    @staticmethod
    def Rem(a: Value, b: Value, unsigned: bool = False) -> Value:
        assert isinstance(a, ConcreteBitVec), a
        assert isinstance(b, ConcreteBitVec), b
        return ConcreteBitVecDomain.Rem(a, b, unsigned)

    @staticmethod
    def Neg(a: Value) -> Value:
        """Return the negated number"""
        if a.is_float():
            return ConcreteFloatsDomain.Neg(a)
        elif a.is_bv():
            return ConcreteBitVecDomain.Neg(a)
        raise NotImplementedError(f"Operation not implemented: Neg({a})")

    @staticmethod
    def Abs(a: Value) -> Value:
        if a.is_float():
            return ConcreteFloatsDomain.Abs(a)
        return ConcreteBitVecDomain.Abs(a)

    @staticmethod
    def FpOp(op, val: ConcreteFloat) -> Union[ConcreteBool, ConcreteBitVec]:
        assert isinstance(val, ConcreteFloat), val
        assert val.is_float(), val

        if op == FpOp.IS_INF:
            return ConcreteBool(isinf(val.value()))
        if op == FpOp.IS_NAN:
            return ConcreteBool(isnan(val.value()))
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.value()
            if isnan(v):
                return ConcreteBitVec(0, 32)
            if isinf(v):
                return ConcreteBitVec(1, 32)
            if v >= 0 and v <= 0:
                return ConcreteBitVec(2, 32)
            if isfinite(v) and v > 1.1754942106924411e-38:
                return ConcreteBitVec(4, 32)
            return ConcreteBitVec(3, 32)  # subnormal
        if op == FpOp.SIGNBIT:
            # FIXME! gosh this is ugly...
            return ConcreteBitVec(1 if str(val.value())[0] == "-" else 0, 32)
        raise NotImplementedError("Invalid/unsupported FP operation")

    ##
    # Relational operators
    @staticmethod
    def Le(a: ConcreteVal, b: ConcreteVal, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Le(a, b, unsigned)
        return ConcreteBitVecDomain.Le(a, b, unsigned)

    @staticmethod
    def Lt(a: ConcreteVal, b: ConcreteVal, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Lt(a, b, unsigned)
        return ConcreteBitVecDomain.Lt(a, b, unsigned)

    @staticmethod
    def Ge(a: ConcreteVal, b: ConcreteVal, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Ge(a, b, unsigned)
        return ConcreteBitVecDomain.Ge(a, b, unsigned)

    @staticmethod
    def Gt(a: ConcreteVal, b: ConcreteVal, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Gt(a, b, unsigned)
        return ConcreteBitVecDomain.Gt(a, b, unsigned)

    @staticmethod
    def Eq(a: Value, b: Value, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(a, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Eq(a, b, unsigned)
        return ConcreteBitVecDomain.Eq(a, b, unsigned)

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if a.is_float():
            return ConcreteFloatsDomain.Ne(a, b, unsigned)
        return ConcreteBitVecDomain.Ne(a, b, unsigned)

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value) -> Value:
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        if a.is_float():
            return ConcreteFloatsDomain.Add(a, b)
        return ConcreteBitVecDomain.Add(a, b)

    @staticmethod
    def Sub(a: ConcreteVal, b: ConcreteVal) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        if a.is_float():
            return ConcreteFloatsDomain.Sub(a, b)
        return ConcreteBitVecDomain.Sub(a, b)

    @staticmethod
    def Mul(
        a: Union[ConcreteBitVec, ConcreteFloat], b: Union[ConcreteBitVec, ConcreteFloat]
    ) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        if a.is_float():
            return ConcreteFloatsDomain.Mul(a, b)
        return ConcreteBitVecDomain.Mul(a, b)

    @staticmethod
    def Div(a: ConcreteBitVec, b: ConcreteBitVec, unsigned: bool = False) -> Value:
        assert isinstance(a, ConcreteVal), a
        assert isinstance(b, ConcreteVal), b
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        if a.is_float():
            ConcreteFloatsDomain.Div(a, b)
        return ConcreteBitVecDomain.Div(a, b)


ConstantTrue = ConcreteBool(True)
ConstantFalse = ConcreteBool(False)
