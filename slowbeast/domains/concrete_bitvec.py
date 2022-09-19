from struct import unpack, pack

from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.ir.types import BitVecType
from .domain import Domain
from .value import Value

def to_unsigned(x, bw: int):
    """Get unsigned value for signed in 2's complement"""
    if isinstance(x, float):
        return int(abs(x))
    if x >= 0:
        return x
    return x + (1 << bw)


def to_signed(x, bw: int):
    """Get signed value for number in 2's complement"""
    if x < (1 << (bw - 1)):
        return x
    return x - (1 << bw)


def to_bv(x, unsigned: bool = True):
    bw = x.bitwidth()
    if x.is_float():
        if bw == 32:
            d = (
                unpack("I", pack("f", x.value()))
                if unsigned
                else unpack("i", pack("f", x.value()))
            )[0]
        else:
            assert bw == 64, f"{x}, bw: {bw}"
            d = (
                unpack("Q", pack("d", x.value()))
                if unsigned
                else unpack("q", pack("d", x.value()))
            )[0]
        return d
    if (x.is_bv() or x.is_bytes()) and not unsigned:
        # signed/unsigned conversion
        uint = to_unsigned(x.value(), bw)
        return (
            unpack(">q", uint.to_bytes(8, "big"))
            if bw == 64
            else unpack(">i", uint.to_bytes(4, "big"))
        )[0]
    return x.value()


def wrap_to_bw(x, bw: int):
    m = 1 << bw
    return x % m


class ConcreteBitVec(ConcreteVal):
    def __init__(self, n: int, bw: int) -> None:
        assert isinstance(n, int), n
        assert isinstance(bw, int), bw
        super().__init__(n, BitVecType(bw))


class ConcreteBitVecsDomain(Domain):
    """
    Takes care of handling concrete bitvec computation. This implementation is based on using Python's int
    and computing the operations modulo.
    """

    @staticmethod
    def belongto(x: Value) -> bool:
        return isinstance(x, ConcreteBitVec)

    @staticmethod
    def Value(c, bw: int) -> ConcreteBitVec:
        return ConcreteBitVec(c, bw)

    ## Relational operations
    # have the default implementation

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert not isfloat
        assert ConcreteBitVecsDomain.belongto(a), a
        assert ConcreteBitVecsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteBitVec(a.unwrap() + b.unwrap(), bw)

    @staticmethod
    def Sub(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert ConcreteBitVecsDomain.belongto(a), a
        assert ConcreteBitVecsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteBitVec(a.unwrap() - b.unwrap(), bw)

    @staticmethod
    def Mul(a: ConcreteBitVec, b: ConcreteBitVec, isfloat: bool = False) -> ConcreteBitVec:
        assert ConcreteBitVecsDomain.belongto(a), a
        assert ConcreteBitVecsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteBitVec(a.unwrap() * b.unwrap(), bw)

    @staticmethod
    def Div(a: ConcreteBitVec, b: ConcreteBitVec, unordered: bool = False, isfloat: bool = False ) -> ConcreteBitVec:
        assert ConcreteBitVecsDomain.belongto(a), a
        assert ConcreteBitVecsDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteBitVec(a.unwrap() / b.unwrap(), bw)

    @staticmethod
    def Eq(a: Value, b: Value,
           unordered: bool = False, floats: bool = False) -> ConcreteBool:
        assert floats
        assert isinstance(a, ConcreteBitVec), f"{a} type: {type(a)}"
        assert isinstance(b, ConcreteBitVec), f"{b} type: {type(b)}"
        return ConcreteBool(a.unwrap() == b.unwrap())
