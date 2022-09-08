from slowbeast.domains.concrete_bool import ConcreteBool
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.domains.value import Value
from slowbeast.ir.types import FloatType


class ConcreteFloat(ConcreteVal):
    def __init__(self, n: float, bw: int) -> None:
        assert isinstance(n, float), n
        assert isinstance(bw, int), bw
        super().__init__(n, FloatType(bw))


class ConcreteFloatsDomain:
    """
    Takes care of handling concrete float computations.
    """

    @staticmethod
    def belongto(*args: Value) -> bool:
        assert len(args) > 0
        for a in args:
            assert isinstance(a, Value), a
            if not (a.is_concrete() and a.is_float()):
                return False
        return True

    @staticmethod
    def Value(c, bw: int) -> ConcreteFloat:
        return ConcreteFloat(float(c), bw)

    ##
    # Relational operators
    @staticmethod
    def Le(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() <= b.value())

    @staticmethod
    def Lt(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() < b.value())

    @staticmethod
    def Ge(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() >= b.value())

    @staticmethod
    def Gt(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        return ConcreteBool(a.value() > b.value())

    @staticmethod
    def Eq(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        aval, bval = a.value(), b.value()
        return ConcreteBool(aval <= bval and aval >= bval)

    @staticmethod
    def Ne(a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False) -> ConcreteBool:
        assert ConcreteFloatsDomain.belongto(a, b)
        if unordered:
            raise NotImplementedError("unordered unimplemented")
        aval, bval = a.value(), b.value()
        return ConcreteBool(aval < bval and aval > bval)

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: ConcreteFloat, b: ConcreteFloat) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() + b.value(), bw)

    @staticmethod
    def Sub(a: ConcreteFloat, b: ConcreteFloat) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() - b.value(), bw)

    @staticmethod
    def Mul(a: ConcreteFloat, b: ConcreteFloat) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        return ConcreteFloat(a.value() * b.value(), bw)

    @staticmethod
    def Div(
        a: ConcreteFloat, b: ConcreteFloat, unordered: bool = False
    ) -> ConcreteFloat:
        assert ConcreteFloatsDomain.belongto(a, b)
        bw = a.bitwidth()
        return ConcreteFloat(a.value() / b.value(), bw)
