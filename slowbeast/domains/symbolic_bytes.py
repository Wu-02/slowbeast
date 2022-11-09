from functools import reduce
from operator import add
from typing import Type, Union, Optional

from slowbeast.ir.types import BytesType
from .domain import Domain
from .expr import Expr
from .symbolic import BVSymbolicDomain
from .symbolic_value import SymbolicBytes
from .value import Value


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
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert isinstance(a, SymbolicBytes), a
        tybw = ty.bitwidth()
        if ty.is_float():
            bv = BVSymbolicDomain.Concat(*a.value())
            return BVSymbolicDomain.Cast(bv, ty, signed)
        elif ty.is_bv():
            return BVSymbolicDomain.Concat(*a.value())
        elif ty.is_bool():
            bv = BVSymbolicDomain.Concat(*a.value())
            return BVSymbolicDomain.Ne(
                bv, BVSymbolicDomain.get_constant(0, bv.bitwidth())
            )
        return None  # unsupported conversion

    @staticmethod
    def Eq(a: Value, b: Value, unsigned: bool = False):
        _check_args(a, b)
        return BVSymbolicDomain.And(
            [BVSymbolicDomain.Eq(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Ne(a: Value, b: Value, unsigned: bool = False):
        _check_args(a, b)
        return BVSymbolicDomain.Not(
            BVSymbolicDomain.And(
                [BVSymbolicDomain.Eq(a, b) for a, b in zip(a.value(), b.value())]
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
            [BVSymbolicDomain.And(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Or(a: Value, b: Value) -> SymbolicBytes:
        _check_args(a, b)
        return SymbolicBytes(
            [BVSymbolicDomain.Or(a, b) for a, b in zip(a.value(), b.value())]
        )

    @staticmethod
    def Xor(a: Value, b: Value) -> SymbolicBytes:
        _check_args(a, b)
        return SymbolicBytes(
            [BVSymbolicDomain.Xor(a, b) for a, b in zip(a.value(), b.value())]
        )
