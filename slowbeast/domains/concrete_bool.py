from slowbeast.domains.concrete_value import ConcreteBool
from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from .domain import Domain
from .value import Value


class ConcreteBoolDomain(Domain):
    @staticmethod
    def get_value(c: bool) -> ConcreteBool:
        assert isinstance(c, bool), c
        return ConcreteBool(c)

    @staticmethod
    def conjunction(*args) -> ConcreteBool:
        """And() of multiple boolean arguments."""
        assert all((isinstance(a, ConcreteBool) for a in args)), args
        assert all((a.is_bool() for a in args))
        return ConcreteBool(all(map(lambda x: x.value() is True, args)))

    @staticmethod
    def disjunction(*args) -> ConcreteBool:
        """Or() of multiple boolean arguments."""
        assert all((isinstance(a, ConcreteBool) for a in args)), args
        assert all((a.is_bool() for a in args))
        return ConcreteBool(any(map(lambda x: x.value() is True, args)))

    @staticmethod
    def And(a: Value, b: Value) -> ConcreteBool:
        assert isinstance(a, ConcreteBool), a
        assert isinstance(b, ConcreteBool), b
        assert a.is_bool(), a
        assert b.is_bool(), b
        return ConcreteBool(a.value() and b.value())

    @staticmethod
    def Or(a: Value, b: Value) -> ConcreteBool:
        assert isinstance(a, ConcreteBool), a
        assert isinstance(b, ConcreteBool), b
        assert a.is_bool(), a
        assert b.is_bool(), b
        return ConcreteBool(a.value() or b.value())

    @staticmethod
    def Xor(a: Value, b: Value) -> ConcreteBool:
        assert isinstance(a, ConcreteBool), a
        assert isinstance(b, ConcreteBool), b
        assert a.is_bool(), a
        assert b.is_bool(), b
        assert a.value() in (True, False), a
        assert b.value() in (True, False), b
        return ConcreteBool(a.value() ^ b.value())

    @staticmethod
    def Not(a: Value) -> ConcreteBool:
        assert isinstance(a, ConcreteBool)
        assert a.is_bool(), a
        assert a.value() in (True, False), a
        return ConcreteBool(not a.value())

    @staticmethod
    def Extend(a: Value, bw: int, unsigned: bool) -> Value:
        assert isinstance(a, ConcreteBool), a
        assert isinstance(bw, int), bw
        assert isinstance(unsigned, bool), unsigned
        assert a.bitwidth() < bw, f"Invalid extend argument: {bw}"
        assert a.is_bool(), a
        return ConcreteBitVec(1 if a.value() else 0, bw)

