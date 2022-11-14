from struct import pack, unpack
from typing import Union

from numpy import (
    float16,
    float32,
    float64,
    isnan,
    isinf,
    isfinite,
    round,
    floor,
    ceil,
    trunc,
)

from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.ir.types import type_mgr, FloatType, Type
from slowbeast.util.debugging import FIXME
from .concrete_bitvec import ConcreteBitVec
from .domain import Domain
from .value import Value
from ..ir.instruction import FpOp


def concrete_float_val_to_bytes(x):
    return [b for b in x.tobytes()]


def float_to_bv(x, bw):
    if bw == 32:
        return (
            unpack("I", pack("f", float(x.value())))
            # if unsigned
            # else unpack("i", pack("f", x.value()))
        )[0]

    assert bw == 64, f"{x}, bw: {bw}"
    return (
        unpack("Q", pack("d", float(x.value())))
        # if unsigned
        # else unpack("q", pack("d", x.value()))
    )[0]


class ConcreteFloat(ConcreteVal):
    def __init__(self, n, bw: Union[Type, int]) -> None:
        if isinstance(bw, FloatType):
            ty = bw
            bw = bw.bitwidth()
        else:
            ty = type_mgr().float_ty(bw)
        assert isinstance(bw, int), bw
        if bw == 16:
            val = float16(n)
        elif bw == 32:
            val = float32(n)
        elif bw == 64:
            val = float64(n)
        else:
            raise NotImplementedError(
                f"ConcreteFloat with bitwidth {bw} not implemented"
            )
        super().__init__(val, ty)

    def is_nan(self) -> bool:
        return isnan(self._value)

    def is_inf(self) -> bool:
        return isinf(self._value)


class ConcreteFloatsDomain(Domain):
    """Takes care of handling concrete float computations."""

    @staticmethod
    def get_value(c, bw: int) -> ConcreteFloat:
        return ConcreteFloat(c, bw)

    ## Relational operations
    @staticmethod
    def Lt(a: ConcreteFloat, b: ConcreteFloat, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:  # means unordered for floats
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or bool(a.value() < b.value()))
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.value() < b.value())
        )

    @staticmethod
    def Gt(a: ConcreteFloat, b: ConcreteFloat, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:  # means unordered for floats
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or bool(a.value() > b.value()))
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.value() > b.value())
        )

    @staticmethod
    def Le(a: ConcreteFloat, b: ConcreteFloat, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:  # means unordered for floats
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or bool(a.value() <= b.value()))
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.value() <= b.value())
        )

    @staticmethod
    def Ge(a: ConcreteFloat, b: ConcreteFloat, unsigned: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:  # means unordered for floats
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or bool(a.value() >= b.value()))
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.value() >= b.value())
        )

    @staticmethod
    def Eq(a: Value, b: Value, unordered: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), f"{a} type: {type(a)}"
        assert isinstance(b, ConcreteFloat), f"{b} type: {type(b)}"
        if unordered:
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or a.unwrap() == b.unwrap())
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.unwrap() == b.unwrap())
        )

    @staticmethod
    def Ne(a: Value, b: Value, unordered: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), f"{a} type: {type(a)}"
        assert isinstance(b, ConcreteFloat), f"{b} type: {type(b)}"
        if unordered:
            return ConcreteBool(
                bool(a.is_nan() or b.is_nan() or a.unwrap() != b.unwrap())
            )
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.unwrap() != b.unwrap())
        )

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() + b.unwrap(), bw)

    @staticmethod
    def Sub(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() - b.unwrap(), bw)

    @staticmethod
    def Mul(a: ConcreteFloat, b: ConcreteFloat) -> ConcreteFloat:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() * b.unwrap(), bw)

    @staticmethod
    def Div(
        a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False
    ) -> ConcreteFloat:
        assert isinstance(a, ConcreteFloat), a
        assert isinstance(b, ConcreteFloat), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = a.value(), b.value()
        if bval == 0:
            # doing the divison works normally, but numpy warns about an error,
            # so silence the warning this way
            if aval == 0:
                return ConcreteFloat("NaN", bw)
            elif aval < 0:
                return ConcreteFloat("-inf", bw)
            elif aval > 0:
                return ConcreteFloat("inf", bw)
            else:
                raise RuntimeError("Invalid value")
        return ConcreteFloat(a.unwrap() / b.unwrap(), bw)

    @staticmethod
    def Abs(a: Value) -> Value:
        assert isinstance(a, ConcreteFloat), a
        return ConcreteFloat(abs(a.value()), a.bitwidth())

    @staticmethod
    def FpOp(op, val: Value, val2: Value):
        assert isinstance(val, ConcreteFloat), val
        assert val.is_float(), val
        assert val2 is None or val2.is_float(), val2

        if op == FpOp.IS_INF:
            return ConcreteBool(isinf(val.value()))
        if op == FpOp.IS_NAN:
            return ConcreteBool(bool(isnan(val.value())))
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
        if op == FpOp.ROUND:
            assert val2 is None, val2
            return ConcreteFloat(round(val.value()), val.type())
        if op == FpOp.FLOOR:
            assert val2 is None, val2
            return ConcreteFloat(floor(val.value()), val.type())
        if op == FpOp.CEIL:
            assert val2 is None, val2
            return ConcreteFloat(ceil(val.value()), val.type())
        if op == FpOp.TRUNC:
            assert val2 is None, val2
            return ConcreteFloat(trunc(val.value()), val.type())
        if op == FpOp.MIN:
            assert val2 is not None
            a, b = val.value(), val2.value()
            if isnan(a):
                return val2
            if isnan(b):
                return val
            assert not (isnan(a) or isnan(b))
            return val if a < b else val2
        if op == FpOp.MAX:
            assert val2 is not None
            a, b = val.value(), val2.value()
            if isnan(a):
                return val2
            if isnan(b):
                return val
            assert not (isnan(a) or isnan(b))
            return val if a > b else val2
        if op == FpOp.DIM:
            assert val2 is not None, val2
            v1, v2 = val.value(), val2.value()
            if isnan(v1) or isnan(v2):
                return val
            # TODO: check for overflow!
            tmp = v1 - v2
            if tmp < 0:
                return ConcreteFloat(0.0, val.type())
            return ConcreteFloat(tmp, val.type())

        raise NotImplementedError("Invalid/unsupported FP operation")

    @staticmethod
    def Neg(a: Value) -> Value:
        """Return the negated number"""
        assert isinstance(a, ConcreteFloat), a
        ty = a.type()
        bw = ty.bitwidth()
        return ConcreteFloat(-a.value(), bw)
