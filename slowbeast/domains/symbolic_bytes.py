from functools import reduce
from operator import add
from typing import Type, Union

from slowbeast.domains.concrete_value import ConcreteBool
from slowbeast.ir.types import BytesType, type_mgr
from .domain import Domain
from .symbolic import SymbolicDomain
from .value import Value


def int_to_bytes(n):
    return [b for b in bytes(n)]


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


class SymbolicBytes(Value):
    """
    A sequence of concrete bitvectors of length 8.
    """

    def __init__(self, values: list) -> None:
        assert isinstance(values, list), values
        assert all((a.bitwidth() == 8 for a in values)), values
        assert all((isinstance(a, Value) for a in values)), values
        ty = type_mgr().bytes_ty(len(values))
        super().__init__(values, ty)


def _check_args(a, b):
    assert isinstance(a, SymbolicBytes), a
    assert isinstance(b, SymbolicBytes), b
    assert a.type() == b.type(), f"{a.type()} != {b.type()}"
    assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"


class SymbolicBytesDomain(Domain):
    """
    Takes care of handling concrete bitvec computation. This implementation is based on using Python's int
    and computing the operations modulo.
    """

    def get_value_cls(self) -> Type[SymbolicBytes]:
        """
        Get the class of values managed by this domain
        """
        return SymbolicBytes

    @staticmethod
    def get_value(values: list, bw: Union[int, BytesType]) -> SymbolicBytes:
        assert 8 * len(values) == bw
        return SymbolicBytes(values)

    @staticmethod
    def Eq(a: Value, b: Value, unsigned: bool = False):
        _check_args(a, b)
        return SymbolicDomain.And(
            [SymbolicDomain.Eq(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False):
        _check_args(a, b)
        return SymbolicDomain.Not(
            SymbolicDomain.And(
                [SymbolicDomain.Eq(a, b) for a, b in zip(a.value(), b.value())]
            )
        )

    @staticmethod
    def Concat(*args) -> Value:
        l = len(args)
        assert l > 0, args
        assert all(map(lambda a: isinstance(a, Value), args)), args
        return SymbolicBytes(reduce(add, args, []))

    # @staticmethod
    # def Extract(a: Value, start: int, end: int) -> Value:
    #    assert isinstance(a, Bytes)
    #    assert isinstance(start, int)
    #    assert isinstance(end, int)
    #    if start % 8 != 0:
    #        # TODO: we could do this better...
    #        return ConcreteBytes(
    #            int_to_bytes(ConcreteBitVecDomain.Extract(to_bv(a.value()), start, end).value())
    #        )
    #    overflow = end % 8
    #    bstart, bend = (start / 8), int(end / 8)
    #    values = a.value()[bstart:bend]
    #    if overflow > 0:
    #        values.append(a.value()[bend + 1] & ((1 << overflow) - 1))
    #    return Bytes(values)

    @staticmethod
    def And(a: Value, b: Value) -> SymbolicBytes:
        _check_args(a, b)
        return SymbolicBytes(
            [SymbolicDomain.And(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Or(a: Value, b: Value) -> SymbolicBytes:
        _check_args(a, b)
        return SymbolicBytes(
            [SymbolicDomain.Or(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Xor(a: Value, b: Value) -> SymbolicBytes:
        _check_args(a, b)
        return SymbolicBytes(
            [SymbolicDomain.Xor(a, b) for a, b in zip(a.value(), b.value())]
        )
