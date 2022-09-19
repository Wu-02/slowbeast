from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.concrete_bool import ConcreteBool
from slowbeast.domains.value import Value
from slowbeast.ir.types import FloatType
from .domain import Domain

from numpy import float16, float32, float64, isnan, isinf


class ConcreteFloat(ConcreteVal):
    def __init__(self, n, bw: int) -> None:
        assert isinstance(bw, int), bw
        if bw == 16:
            val = float16(n)
        elif bw == 32:
            val = float32(n)
        elif bw == 64:
            val = float64(n)
        else:
            raise NotImplementedError(f"ConcreteFloat with bitwidth {bw} not implemented")
        super().__init__(val, FloatType(bw))

    def is_nan(self) -> bool:
        return isnan(self._value)

    def is_inf(self) -> bool:
        return isinf(self._value)


class ConcreteFloatsDomain(Domain):
    """ Takes care of handling concrete float computations. """

    @staticmethod
    def belongto(x: Value) -> bool:
        return isinstance(x, ConcreteFloat)

    @staticmethod
    def Value(c, bw: int) -> ConcreteFloat:
        return ConcreteFloat(c, bw)

    ## Relational operations
    # have the default implementation

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value) -> Value:
        assert ConcreteFloatsDomain.belongto(a), a
        assert ConcreteFloatsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() + b.unwrap(), bw)

    @staticmethod
    def Sub(a: Value, b: Value) -> Value:
        assert ConcreteFloatsDomain.belongto(a), a
        assert ConcreteFloatsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() - b.unwrap(), bw)

    @staticmethod
    def Mul(a: ConcreteFloat, b: ConcreteFloat) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a), a
        assert ConcreteFloatsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() * b.unwrap(), bw)

    @staticmethod
    def Div(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False ) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a), a
        assert ConcreteFloatsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() / b.unwrap(), bw)

    @staticmethod
    def Eq(a: Value, b: Value,
           unordered: bool = False, floats: bool = False) -> ConcreteBool:
        assert floats
        assert isinstance(a, ConcreteFloat), f"{a} type: {type(a)}"
        assert isinstance(b, ConcreteFloat), f"{b} type: {type(b)}"
        return ConcreteBool(bool(not a.is_nan() and not b.is_nan() and a.unwrap() == b.unwrap()))
