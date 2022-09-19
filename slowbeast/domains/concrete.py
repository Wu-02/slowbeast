from math import isinf, isnan, isfinite
from struct import pack, unpack

from slowbeast.ir.instruction import FpOp
from slowbeast.ir.types import BitVecType, Type, FloatType
from slowbeast.util.debugging import FIXME
from .concrete_bitvec import (
    to_unsigned,
    to_bv,
    wrap_to_bw,
    ConcreteBitVec,
    ConcreteBitVecsDomain,
)
from .domain import Domain
from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.domains.concrete_bool import ConcreteBoolDomain
from slowbeast.domains.concrete_floats import ConcreteFloat, ConcreteFloatsDomain
from typing import Optional, Union


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
    def belongto(x) -> bool:
        return isinstance(x, ConcreteVal)

    @staticmethod
    def Value(c, bw: int) -> ConcreteVal:
        if isinstance(c, bool):
            assert bw == 1, bw
            return ConcreteBool(c)
        if isinstance(c, int):
            return ConcreteBitVec(c, bw)
        if isinstance(c, float):
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
        assert ConcreteDomain.belongto(c), c
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return a if c else b

    @staticmethod
    def And(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.And(a, b)
        elif a.is_bv():
            return ConcreteBitVecsDomain.And(a, b)
        raise NotImplementedError(f"Operation not implemented: And({a}, {b})")

    @staticmethod
    def Or(a, b) -> ConcreteVal:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.Or(a, b)
        elif a.is_bv():
            return ConcreteBitVecsDomain.Or(a, b)
        raise NotImplementedError(f"Operation not implemented: Or({a}, {b})")

    @staticmethod
    def Xor(a, b) -> ConcreteVal:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBoolDomain.Xor(a, b)
        elif a.is_bv():
            return ConcreteBitVec(to_bv(a) ^ to_bv(b), a.bitwidth())
        raise NotImplementedError(f"Operation not implemented: Xor({a}, {b})")

    @staticmethod
    def Not(a) -> ConcreteVal:
        assert ConcreteDomain.belongto(a)
        if a.is_bool():
            return ConcreteBoolDomain.Not(a)
        raise NotImplementedError(f"Operation not implemented: Not({a})")

    @staticmethod
    def ZExt(a, b) -> Value:
        return ConcreteBitVecsDomain.ZExt(a, b)

    @staticmethod
    def SExt(a, b) -> Value:
        return ConcreteBitVecsDomain.SExt(a, b)

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = False) -> Optional[Value]:
        """Reinterpret cast"""

        assert ConcreteDomain.belongto(a), a
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
        assert ConcreteDomain.belongto(a), a
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
        return ConcreteBitVecsDomain.Shl(a, b)

    @staticmethod
    def AShr(a: Value, b: Value) -> Value:
        return ConcreteBitVecsDomain.AShr(a, b)

    @staticmethod
    def LShr(a: Value, b: Value) -> Value:
        return ConcreteBitVecsDomain.LShr(a, b)

    @staticmethod
    def Extract(a: Value, start: ConcreteVal, end: ConcreteVal) -> Value:
        return ConcreteBitVecsDomain.Extract(a, start, end)

    @staticmethod
    def Concat(*args) -> Value:
        return ConcreteBitVecsDomain.Concat(*args)

    @staticmethod
    def Rem(a: Value, b: Value, unsigned: bool = False) -> Value:
        return ConcreteBitVecsDomain.Rem(a, b, unsigned)

    @staticmethod
    def Neg(a: Value, isfloat: bool = False) -> Value:
        """Return the negated number"""
        if isfloat:
            return ConcreteFloatsDomain.Neg(a, True)
        elif a.is_bv():
            return ConcreteBitVecsDomain.Neg(a, isfloat)
        raise NotImplementedError(f"Operation not implemented: Neg({a})")

    @staticmethod
    def Abs(a: Value) -> Value:
        # FIXME: what about floats?
        return ConcreteBitVecsDomain.Abs(a)

    @staticmethod
    def FpOp(op, val) -> Union[ConcreteBool, ConcreteBitVec]:
        assert ConcreteDomain.belongto(val)
        # FIXME: do not use the enum from instruction
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
    def Le(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Le(a, b, unsigned, True)

        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) <= to_unsigned(bval, bw))
        return ConcreteBool(aval <= bval)

    @staticmethod
    def Lt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Lt(a, b, unsigned, True)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) < to_unsigned(bval, bw))
        return ConcreteBool(aval < bval)

    @staticmethod
    def Ge(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Ge(a, b, unsigned, True)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) >= to_unsigned(bval, bw))
        return ConcreteBool(aval >= bval)

    @staticmethod
    def Gt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Gt(a, b, unsigned, True)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) > to_unsigned(bval, bw))
        return ConcreteBool(aval > bval)

    @staticmethod
    def Eq(
        a: Value, b: Value, unsigned: bool = False, floats: bool = False
    ) -> ConcreteBool:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Eq(a, b, unsigned, floats)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) == to_unsigned(bval, bw))
        return ConcreteBool(aval == bval)

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False, floats: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            return ConcreteFloatsDomain.Ne(a, b, unsigned, floats)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) != to_unsigned(bval, bw))
        return ConcreteBool(aval != bval)

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a, b, isfloat: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Add(a, b)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval + bval, bw), BitVecType(bw))

    @staticmethod
    def Sub(a, b, isfloat: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Sub(a, b)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval - bval, bw), BitVecType(bw))

    @staticmethod
    def Mul(a, b, isfloat: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Mul(a, b)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval * bval, bw), BitVecType(bw))

    @staticmethod
    def Div(a, b, unsigned: bool = False, isfloat: bool = False) -> Value:
        assert ConcreteDomain.belongto(a), a
        assert ConcreteDomain.belongto(b), b
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_bv() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            ConcreteFloatsDomain.Div(a, b, isfloat)
        result_ty = BitVecType(bw)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            return ConcreteVal(to_unsigned(aval, bw) / to_unsigned(bval, bw), result_ty)
        return ConcreteVal(wrap_to_bw(int(aval / bval), bw), result_ty)


ConstantTrue = ConcreteBool(True)
ConstantFalse = ConcreteBool(False)
