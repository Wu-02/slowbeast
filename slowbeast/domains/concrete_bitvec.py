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


class ConcreteBitVecDomain(Domain):
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
    @staticmethod
    def Le(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert not floats
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) <= to_unsigned(bval, bw))
        return ConcreteBool(aval <= bval)

    @staticmethod
    def Lt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert not floats
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) < to_unsigned(bval, bw))
        return ConcreteBool(aval < bval)

    @staticmethod
    def Ge(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert not floats
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) >= to_unsigned(bval, bw))
        return ConcreteBool(aval >= bval)

    @staticmethod
    def Gt(a, b, unsigned: bool = False, floats: bool = False) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        assert not floats
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) > to_unsigned(bval, bw))
        return ConcreteBool(aval > bval)

    @staticmethod
    def Eq(
        a: Value, b: Value, unsigned: bool = False, floats: bool = False
    ) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) == to_unsigned(bval, bw))
        return ConcreteBool(aval == bval)

    @staticmethod
    def Ne(
        a: Value, b: Value, unsigned: bool = False, floats: bool = False
    ) -> ConcreteBool:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) != to_unsigned(bval, bw))
        return ConcreteBool(aval != bval)

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert not isfloat
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBitVec(wrap_to_bw(aval + bval, bw), bw)

    @staticmethod
    def Sub(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBitVec(wrap_to_bw(aval - bval, bw), bw)

    @staticmethod
    def Mul(
        a: ConcreteBitVec, b: ConcreteBitVec, isfloat: bool = False
    ) -> ConcreteBitVec:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBitVec(wrap_to_bw(aval * bval, bw), bw)

    @staticmethod
    def Div(
        a: ConcreteBitVec,
        b: ConcreteBitVec,
        unordered: bool = False,
        isfloat: bool = False,
    ) -> ConcreteBitVec:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a, unordered), to_bv(b, unordered)
        if unordered:
            return ConcreteBitVec(to_unsigned(aval, bw) / to_unsigned(bval, bw), bw)
        return ConcreteBitVec(wrap_to_bw(int(aval / bval), bw), bw)

    @staticmethod
    def ZExt(a: Value, b: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        assert a.is_bv(), a
        aval = to_bv(a, unsigned=True)
        return ConcreteBitVec(to_unsigned(aval, a.bitwidth()), b.value())

    @staticmethod
    def SExt(a: Value, b: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        assert a.is_bv(), a
        return ConcreteBitVec(a.value(), b.value())

    @staticmethod
    def Shl(a: Value, b: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert b.is_bv(), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteBitVec(to_bv(a) << b.value(), bw)

    @staticmethod
    def AShr(a: Value, b: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert b.is_bv(), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteBitVec(to_bv(a) >> b.value(), bw)

    @staticmethod
    def LShr(a: Value, b: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert b.is_bv(), b
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = to_bv(a)
        bw = a.bitwidth()
        return ConcreteBitVec(
            to_bv(a) >> b.value() if val >= 0 else (val + (1 << bw)) >> b.value(),
            bw,
        )

    @staticmethod
    def Extract(a: Value, start: ConcreteVal, end: ConcreteVal) -> Value:
        assert ConcreteBitVecDomain.belongto(a)
        assert start.is_concrete(), start
        assert end.is_concrete(), end
        bitsnum = end.value() - start.value() + 1
        return ConcreteBitVec(
            (to_bv(a) >> start.value()) & ((1 << (bitsnum)) - 1), bitsnum
        )

    @staticmethod
    def Concat(*args) -> Value:
        l = len(args)
        assert l > 0, args
        assert all(map(lambda a: ConcreteBitVecDomain.belongto(a), args)), args

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
    def Rem(a: Value, b: Value, unsigned: bool = False) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        assert ConcreteBitVecDomain.belongto(b), b
        assert b.value() != 0, "Invalid remainder"
        bw = a.bitwidth()
        if unsigned:
            return ConcreteBitVec(
                to_unsigned(to_bv(a), bw) % to_unsigned(to_bv(b), b.bitwidth()),
                bw,
            )
        return ConcreteBitVec(a.value() % b.value(), bw)

    @staticmethod
    def Neg(a: Value, isfloat: bool = False) -> Value:
        """Return the negated number"""
        assert ConcreteBitVecDomain.belongto(a), a
        ty = a.type()
        bw = ty.bitwidth()
        return ConcreteBitVec(wrap_to_bw(-a.value(), bw), bw)

    @staticmethod
    def Abs(a: Value) -> Value:
        assert ConcreteBitVecDomain.belongto(a), a
        return ConcreteBitVec(abs(a.value()), a.bitwidth())
