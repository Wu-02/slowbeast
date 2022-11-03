from struct import unpack
from typing import Type, Union

from slowbeast.domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.ir.types import BytesType
from .domain import Domain
from .value import Value


def to_unsigned(x: int, bw: int) -> int:
    """Get unsigned value for signed in 2's complement"""
    assert not isinstance(x, float), x
    if x >= 0:
        return x
    return x + (1 << bw)


def to_signed(x: int, bw: int) -> int:
    """Get signed value for number in 2's complement"""
    if x < (1 << (bw - 1)):
        return x
    return x - (1 << bw)


def to_bv(x, unsigned: bool = True):
    bw = x.bitwidth()
    assert not x.is_float(), x
    if unsigned:
        # signed/unsigned conversion
        uint = to_unsigned(x.value(), bw)
        return (
            unpack(">q", uint.to_bytes(8, "big"))
            if bw == 64
            else unpack(">i", uint.to_bytes(4, "big"))
        )[0]
    return x.value()


def wrap_to_bw(x, bw: int):
    return x % (1 << bw)


class ConcreteBytes(ConcreteVal):
    """
    A sequence of concrete bytes. We represent them as Python int, so they are basically the same as ConcreteBitVec right now.
    """

    def __init__(self, n: int, byteswidth: Union[int, BytesType]) -> None:
        assert isinstance(n, int), n
        if not isinstance(byteswidth, BytesType):
            assert isinstance(byteswidth, int), byteswidth
            byteswidth = BytesType(byteswidth)
        super().__init__(n, byteswidth)


def _check_args(a, b):
    assert isinstance(a, ConcreteBytes), a
    assert isinstance(b, ConcreteBytes), b
    assert a.type() == b.type(), f"{a.type()} != {b.type()}"
    assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"


class ConcreteBytesDomain(Domain):
    """
    Takes care of handling concrete bitvec computation. This implementation is based on using Python's int
    and computing the operations modulo.
    """

    def get_value_cls(self) -> Type[ConcreteBytes]:
        """
        Get the class of values managed by this domain
        """
        return ConcreteBytes

    @staticmethod
    def get_value(c: int, bw: Union[int, BytesType]) -> ConcreteBytes:
        return ConcreteBytes(c, bw)

    ## Relational operations
    @staticmethod
    def Le(a: ConcreteBytes, b: ConcreteBytes, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) <= to_unsigned(bval, bw))
        return ConcreteBool(aval <= bval)

    @staticmethod
    def Lt(a: ConcreteBytes, b: ConcreteBytes, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) < to_unsigned(bval, bw))
        return ConcreteBool(aval < bval)

    @staticmethod
    def Ge(a: ConcreteBytes, b: ConcreteBytes, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) >= to_unsigned(bval, bw))
        return ConcreteBool(aval >= bval)

    @staticmethod
    def Gt(a: ConcreteBytes, b: ConcreteBytes, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) > to_unsigned(bval, bw))
        return ConcreteBool(aval > bval)

    @staticmethod
    def Eq(a: Value, b: Value, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) == to_unsigned(bval, bw))
        return ConcreteBool(aval == bval)

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
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
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBytes(wrap_to_bw(aval + bval, bw), bw)

    @staticmethod
    def Sub(a: Value, b: Value, isfloat: bool = False) -> Value:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBytes(wrap_to_bw(aval - bval, bw), bw)

    @staticmethod
    def Mul(a: ConcreteBytes, b: ConcreteBytes, isfloat: bool = False) -> ConcreteBytes:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a), to_bv(b)
        return ConcreteBytes(wrap_to_bw(aval * bval, bw), bw)

    @staticmethod
    def Div(
        a: ConcreteBytes,
        b: ConcreteBytes,
        unsigned: bool = False,
    ) -> ConcreteBytes:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        aval, bval = to_bv(a, unsigned), to_bv(b, unsigned)
        return ConcreteBytes(wrap_to_bw(int(aval / bval), bw), bw)

    @staticmethod
    def Extend(a: Value, bw: int, unsigned: bool) -> Value:
        assert isinstance(a, ConcreteBytes), f"{a} {type(a)}"
        assert isinstance(bw, int), bw
        assert isinstance(unsigned, bool), unsigned
        assert a.bitwidth() < bw, f"Invalid extend argument: {bw}"
        aval = to_bv(a, unsigned)
        return ConcreteBytes(aval, bw)

    @staticmethod
    def Shl(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteBytes(to_bv(a) << b.value(), bw)

    @staticmethod
    def AShr(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        bw = a.bitwidth()
        assert b.value() < bw, "Invalid shift"
        return ConcreteBytes(to_bv(a) >> b.value(), bw)

    @staticmethod
    def LShr(a: Value, b: Value) -> Value:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = to_bv(a)
        bw = a.bitwidth()
        return ConcreteBytes(
            to_bv(a) >> b.value() if val >= 0 else (val + (1 << bw)) >> b.value(),
            bw,
        )

    @staticmethod
    def Extract(a: Value, start: int, end: int) -> Value:
        assert isinstance(a, ConcreteBytes)
        assert isinstance(start, int)
        assert isinstance(end, int)
        bitsnum = end - start + 1
        return ConcreteBytes((to_bv(a) >> start) & ((1 << (bitsnum)) - 1), bitsnum)

    @staticmethod
    def Concat(*args) -> Value:
        l = len(args)
        assert l > 0, args
        assert all(map(lambda a: isinstance(a, ConcreteBytes), args)), args

        if l == 1:
            return args[0]
        bw = 0
        val = 0
        for i in range(1, l + 1):
            a = args[l - i]
            val |= a.value() << bw
            bw += a.bitwidth()
        return ConcreteBytes(val, int(bw / 8))

    @staticmethod
    def Rem(a: Value, b: Value, unsigned: bool = False) -> Value:
        assert isinstance(a, ConcreteBytes), a
        assert isinstance(b, ConcreteBytes), b
        assert b.value() != 0, "Invalid remainder"
        bw = a.bitwidth()
        if unsigned:
            return ConcreteBytes(
                to_unsigned(to_bv(a), bw) % to_unsigned(to_bv(b), b.bitwidth()),
                bw,
            )
        return ConcreteBytes(a.value() % b.value(), bw)

    @staticmethod
    def Neg(a: Value) -> Value:
        """Return the negated number"""
        assert isinstance(a, ConcreteBytes), a
        ty = a.type()
        bw = ty.bitwidth()
        return ConcreteBytes(wrap_to_bw(-a.value(), bw), bw)

    @staticmethod
    def Abs(a: Value) -> Value:
        assert isinstance(a, ConcreteBytes), a
        return ConcreteBytes(abs(a.value()), a.bitwidth())

    @staticmethod
    def And(a: Value, b: Value) -> ConcreteBytes:
        assert isinstance(a, ConcreteBytes) and isinstance(b, ConcreteBytes)
        assert a.type() == b.type(), f"{a}, {b}"
        return ConcreteBytes(a.value() & b.value(), a.bitwidth())

    @staticmethod
    def Or(a: Value, b: Value) -> ConcreteBytes:
        assert isinstance(a, ConcreteBytes) and isinstance(b, ConcreteBytes)
        assert a.type() == b.type(), f"{a}, {b}"
        return ConcreteBytes(a.value() | b.value(), a.bitwidth())

    @staticmethod
    def Xor(a: Value, b: Value) -> ConcreteBytes:
        assert isinstance(a, ConcreteBytes) and isinstance(b, ConcreteBytes)
        assert a.type() == b.type(), f"{a}, {b}"
        return ConcreteBytes(a.value() ^ b.value(), a.bitwidth())