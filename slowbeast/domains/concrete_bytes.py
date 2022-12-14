from functools import reduce
from operator import add
from typing import Union

from slowbeast.domains.concrete_value import ConcreteBool, ConcreteVal
from slowbeast.ir.types import BytesType, type_mgr
from .concrete_bitvec import ConcreteBitVec, ConcreteBitVecDomain
from .domain import Domain
from .value import Value


def int_to_bytes(n, bw):
    return [b for b in n.to_bytes(length=bw, byteorder="little", signed=(n < 0))]


def to_bv(values: list):
    l = len(values)
    if l == 1:
        return values[0]
    bw = 0
    val = 0
    for i in range(1, l + 1):
        a = values[l - i]
        val |= a << bw
        bw += 8
    return val


class ConcreteBytes(ConcreteVal):
    """
    A sequence of concrete bitvectors of length 8.
    """

    def __init__(self, values: list) -> None:
        assert isinstance(values, list), values
        assert all((a.bitwidth() == 8 for a in values)), values
        assert all((isinstance(a, ConcreteBitVec) for a in values)), values
        ty = type_mgr().bytes_ty(len(values))
        super().__init__(values, ty)

    def is_symbolic(self):
        return any((v.is_symbolic() for v in self.value()))

    def to_bv(self):
        return ConcreteBitVecDomain.Concat(*self.value())

    def from_string(s):
        assert all((c.isascii() for c in s)), s
        return ConcreteBytes([ConcreteBitVec(ord(c), 8) for c in s])


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

    def get_value_cls(self):
        """
        Get the class of values managed by this domain
        """
        return ConcreteBytes

    @staticmethod
    def get_value(values: list, bw: Union[int, BytesType]) -> ConcreteBytes:
        assert 8 * len(values) == bw
        return ConcreteBytes(values)

    @staticmethod
    def Eq(a: Value, b: Value, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        return ConcreteBool(a.value() == b.value())

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False) -> ConcreteBool:
        _check_args(a, b)
        return ConcreteBool(a.value() != b.value())

    @staticmethod
    def Extract(a: Value, start: int, end: int) -> Value:
        assert isinstance(a, ConcreteBytes)
        assert isinstance(start, int)
        assert isinstance(end, int)
        if start % 8 != 0:
            # TODO: we could do this better...
            val = ConcreteBitVecDomain.Extract(to_bv(a.value()), start, end)
            return ConcreteBytes(int_to_bytes(val.value(), val.bytewidth()))
        overflow = end % 8
        bstart, bend = (start / 8), int(end / 8)
        values = a.value()[bstart:bend]
        if overflow > 0:
            values.append(a.value()[bend + 1] & ((1 << overflow) - 1))
        return ConcreteBytes(values)

    @staticmethod
    def Concat(*args) -> Value:
        l = len(args)
        assert l > 0, args
        assert all(map(lambda a: isinstance(a, ConcreteBytes), args)), args
        return ConcreteBytes(reduce(add, args, []))

    @staticmethod
    def And(a: Value, b: Value) -> ConcreteBytes:
        _check_args(a, b)
        return ConcreteBytes([a & b for a, b in zip(a.value(), b.value())])

    @staticmethod
    def Or(a: Value, b: Value) -> ConcreteBytes:
        _check_args(a, b)
        return ConcreteBytes([a | b for a, b in zip(a.value(), b.value())])

    @staticmethod
    def Xor(a: Value, b: Value) -> ConcreteBytes:
        _check_args(a, b)
        return ConcreteBytes([a ^ b for a, b in zip(a.value(), b.value())])
