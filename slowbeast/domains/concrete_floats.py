from numpy import float16, float32, float64, isnan, isinf

from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.ir.types import type_mgr, FloatType
from .domain import Domain
from .value import Value


# def float_to_bv(x):
#     if bw == 32:
#         d = (
#             unpack("I", pack("f", x.value()))
#             if unsigned
#             else unpack("i", pack("f", x.value()))
#         )[0]
#     else:
#         assert bw == 64, f"{x}, bw: {bw}"
#         d = (
#             unpack("Q", pack("d", x.value()))
#             if unsigned
#             else unpack("q", pack("d", x.value()))
#         )[0]
#     return d


class ConcreteFloat(ConcreteVal):
    def __init__(self, n, bw: int) -> None:
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
            return ConcreteBool(bool(a.value() < b.value()))
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
            return ConcreteBool(bool(a.value() > b.value()))
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
            return ConcreteBool(bool(a.value() <= b.value()))
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
            return ConcreteBool(bool(a.value() >= b.value()))
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.value() >= b.value())
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
        return ConcreteFloat(a.unwrap() / b.unwrap(), bw)

    @staticmethod
    def Eq(a: Value, b: Value, unordered: bool = False) -> ConcreteBool:
        assert isinstance(a, ConcreteFloat), f"{a} type: {type(a)}"
        assert isinstance(b, ConcreteFloat), f"{b} type: {type(b)}"
        return ConcreteBool(
            bool(not a.is_nan() and not b.is_nan() and a.unwrap() == b.unwrap())
        )

    @staticmethod
    def Abs(a: Value) -> Value:
        assert isinstance(a, ConcreteFloat), a
        return ConcreteFloat(abs(a.value()), a.bitwidth())
