from math import isinf, isnan, isfinite
from struct import pack, unpack

from slowbeast.ir.instruction import FpOp
from slowbeast.ir.types import BitVecType, Type, FloatType
from slowbeast.util.debugging import FIXME
from . import dom_is_concrete
from .concrete_bitvec import to_unsigned, to_bv, wrap_to_bw, ConcreteBitVec
from .domain import Domain
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.domains.concrete_bool import ConcreteBool
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


# FIXME: this concrete domain contains Ints and Floats... separate them and then create
# ConcreteFloatIntDomain (it will have easier implementation)
class ConcreteIntFloatDomain(Domain):
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
        raise NotImplementedError("Don't know how to create a ConcretValue for {c}: {type(c)}")

    @staticmethod
    def get_true() -> ConcreteBool:
        return ConcreteBool(True)

    @staticmethod
    def get_false() -> ConcreteBool:
        return ConcreteBool(False)

    @staticmethod
    def conjunction(*args) -> ConcreteBool:
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert ConcreteIntFloatDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteBool(all(map(lambda x: x.value() is True, args)))

    @staticmethod
    def disjunction(*args) -> ConcreteBool:
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert ConcreteIntFloatDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteBool(any(map(lambda x: x.value() is True, args)))

    @staticmethod
    def Ite(c: Value, a: Value, b: Value):
        assert dom_is_concrete(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return a if c else b

    @staticmethod
    def And(a: Value, b: Value) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBool(a.value() and b.value())
        else:
            return ConcreteVal(to_bv(a) & to_bv(b), BitVecType(a.bitwidth()))

    @staticmethod
    def Or(a, b) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBool(a.value() or b.value())
        else:
            return ConcreteVal(to_bv(a) | to_bv(b), BitVecType(a.bitwidth()))

    @staticmethod
    def Xor(a, b) -> ConcreteVal:
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        return ConcreteBitVec(to_bv(a) ^ to_bv(b), a.bitwidth())

    @staticmethod
    def Not(a) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a)
        if a.is_bool():
            return ConcreteBool(not a.value())
        else:
            raise NotImplementedError("Not implemented")

    @staticmethod
    def ZExt(a, b) -> ConcreteBitVec:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        aval = to_bv(a, unsigned=True)
        return ConcreteBitVec(to_unsigned(aval, a.bitwidth()), b.value())

    @staticmethod
    def SExt(a, b) -> ConcreteBitVec:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        assert a.is_int() is not None, a
        # FIXME: support bytes...
        # sb = 1 << (b.value() - 1)
        # aval = to_bv(a, unsigned=False)
        # val = (aval & (sb - 1)) - (aval & sb)
        # return ConcreteBitVec(val, b.value())
        return ConcreteBitVec(a.value(), b.value())

    @staticmethod
    def Cast(a: ConcreteVal, ty: Type) -> Optional[ConcreteVal]:
        """ Reinterpret cast """

        assert ConcreteIntFloatDomain.belongto(a), a
        bw = ty.bitwidth()
        if a.is_bool() and ty.is_int():
            return ConcreteBitVec(1 if a.value() != 0 else 0, bw)
        if a.is_bytes() and ty.is_float():
            return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
        if a.is_int():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(float(a.value()), bw), bw)
            elif ty.is_int():
                return ConcreteBitVec(a.value(), bw)
            elif ty.is_bool():
                return ConcreteBool(False if a.value() == 0 else True)
        elif a.is_float():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(a.value(), bw), bw)
            elif ty.is_int():
                return ConcreteBitVec(int(a.value()), bw)
        return None  # unsupported conversion

    @staticmethod
    def BitCast(a: ConcreteVal, ty: Type) -> Optional[ConcreteVal]:
        """static cast"""
        assert ConcreteIntFloatDomain.belongto(a), a
        bw = ty.bitwidth()
        if a.is_bool() and ty.is_int():
            return ConcreteBitVec(1 if a.value() else 0, bw)
        if a.is_bytes() and ty.is_float():
            return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
        if a.is_int():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(to_fp(a), bw), bw)
            elif ty.is_int():
                return ConcreteBitVec(a.value(), bw)
            elif ty.is_bool():
                return ConcreteBool(False if a.value() == 0 else True)
        elif a.is_float():
            if ty.is_float():
                return ConcreteFloat(trunc_to_float(a.value(), bw), bw)
            elif ty.is_int():
                return ConcreteBitVec(to_bv(a), bw)
        return None  # unsupported conversion

    @staticmethod
    def Shl(a, b) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert b.is_int(), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteVal(to_bv(a) << b.value(), BitVecType(bw))

    @staticmethod
    def AShr(a, b) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert b.is_int(), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteVal(to_bv(a) >> b.value(), BitVecType(bw))

    @staticmethod
    def LShr(a, b) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert b.is_int(), b
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = to_bv(a)
        bw = a.bitwidth()
        return ConcreteVal(
            to_bv(a) >> b.value() if val >= 0 else (val + (1 << bw)) >> b.value(),
            BitVecType(bw),
        )

    @staticmethod
    def Extract(a, start, end) -> ConcreteBitVec:
        assert ConcreteIntFloatDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        bitsnum = end.value() - start.value() + 1
        return ConcreteBitVec(
            (to_bv(a) >> start.value()) & ((1 << (bitsnum)) - 1), bitsnum
        )

    @staticmethod
    def Concat(*args):
        l = len(args)
        assert l > 0, args
        assert ConcreteIntFloatDomain.belongto(*args), args
        if l == 1:
            return args[0]
        bw = 0
        val = 0
        for i in range(1, l + 1):
            a = args[l - i]
            val |= a.value() << bw
            bw += a.bitwidth()
        return ConcreteBitVec(val, bw)

    @staticmethod
    def Rem(a, b, unsigned: bool = False) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert b.value() != 0, "Invalid remainder"
        if unsigned:
            return ConcreteVal(
                to_unsigned(to_bv(a), a.bitwidth())
                % to_unsigned(to_bv(b), b.bitwidth()),
                a.type(),
            )
        return ConcreteVal(a.value() % b.value(), a.type())

    @staticmethod
    def Neg(a, isfloat) -> ConcreteVal:
        """Return the negated number"""
        assert ConcreteIntFloatDomain.belongto(a)
        ty = a.type()
        bw = ty.bitwidth()
        if isfloat:
            return ConcreteVal(trunc_to_float(-to_fp(a), ty.bitwidth()), FloatType(bw))
        return ConcreteVal(wrap_to_bw(-a.value(), ty.bitwidth()), ty)

    @staticmethod
    def Abs(a) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a)
        return ConcreteVal(abs(a.value()), a.type())

    @staticmethod
    def FpOp(op, val) -> Union[ConcreteBool, ConcreteBitVec]:
        assert ConcreteIntFloatDomain.belongto(val)
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
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = to_fp(a, unsigned), to_fp(b, unsigned)
            if unsigned:  # means unordered for floats
                return ConcreteBool(aval <= bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval <= bval)

        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) <= to_unsigned(bval, bw))
        return ConcreteBool(aval <= bval)

    @staticmethod
    def Lt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = to_fp(a, unsigned), to_fp(b, unsigned)
            if unsigned:  # means unordered for floats
                return ConcreteBool(aval < bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval < bval)

        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) < to_unsigned(bval, bw))
        return ConcreteBool(aval < bval)

    @staticmethod
    def Ge(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = to_fp(a, unsigned), to_fp(b, unsigned)
            if unsigned:  # means unordered for floats
                return ConcreteBool(aval >= bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval >= bval)

        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) >= to_unsigned(bval, bw))
        return ConcreteBool(aval >= bval)

    @staticmethod
    def Gt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = to_fp(a, unsigned), to_fp(b, unsigned)
            if unsigned:  # means unordered for floats
                return ConcreteBool(aval > bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval > bval)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) > to_unsigned(bval, bw))
        return ConcreteBool(aval > bval)

    @staticmethod
    def Eq(a: Value, b: Value,
           unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
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
    def Ne(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
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
    def Add(a, b, isfloat: bool = False) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float() or a.is_bytes()
        # FIXME: add self-standing float domain
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Add(a, b)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval + bval, bw), BitVecType(bw))

    @staticmethod
    def Sub(a, b, isfloat: bool = False) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Sub(a, b, isfloat)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval - bval, bw), BitVecType(bw))

    @staticmethod
    def Mul(a, b, isfloat: bool = False) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float() or a.is_bytes()
        bw = a.bitwidth()
        if isfloat:
            return ConcreteFloatsDomain.Mul(a, b, isfloat)
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteVal(wrap_to_bw(aval * bval, bw), BitVecType(bw))

    @staticmethod
    def Div(a, b, unsigned: bool = False, isfloat: bool = False) -> ConcreteVal:
        assert ConcreteIntFloatDomain.belongto(a), a
        assert ConcreteIntFloatDomain.belongto(b), b
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float() or a.is_bytes()
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
