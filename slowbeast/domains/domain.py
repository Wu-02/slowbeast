from slowbeast.ir.types import Type
from .value import Value
from .concrete_value import ConcreteBool

from typing import Optional


def not_implemented():
    raise NotImplementedError("Child class must reimplement")


class Domain:
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    KIND = None

    @staticmethod
    def lift(v: Value):
        return not_implemented()

    @staticmethod
    def simplify(v: Value) -> Value:
        return not_implemented()

    @staticmethod
    def to_python_constant(val: Value):
        return not_implemented()

    @staticmethod
    def substitute(v: Value, *what) -> Value:
        return not_implemented()

    @staticmethod
    def Value(c, bw: int) -> Value:
        return not_implemented()

    ##
    # Logic operators
    @staticmethod
    def conjunction(*args) -> Value:
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        return not_implemented()

    @staticmethod
    def disjunction(*args) -> Value:
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        return not_implemented()

    @staticmethod
    def Ite(c: Value, a: Value, b: Value) -> Value:
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return not_implemented()

    @staticmethod
    def And(a: Value, b: Value) -> Value:
        assert a.type() == b.type(), f"{a}, {b}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        return not_implemented()

    @staticmethod
    def Or(a: Value, b: Value) -> Value:
        assert a.type() == b.type(), f"{a}, {b}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        return not_implemented()

    @staticmethod
    def Xor(a: Value, b: Value) -> Value:
        assert a.type() == b.type(), f"{a}, {b}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        return not_implemented()

    @staticmethod
    def Not(a: Value) -> Value:
        return not_implemented()

    @staticmethod
    def ZExt(a: Value, b: Value) -> Value:
        return not_implemented()

    @staticmethod
    def SExt(a, b) -> Value:
        return not_implemented()

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Value]:
        """Static cast"""
        return not_implemented()

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Value]:
        """Reinterpret cast"""
        return not_implemented()

    @staticmethod
    def Extract(a, start, end) -> Value:
        return not_implemented()

    @staticmethod
    def Concat(*args):
        return not_implemented()

    @staticmethod
    def Shl(a, b) -> Value:
        return not_implemented()

    @staticmethod
    def AShr(a, b) -> Value:
        return not_implemented()

    @staticmethod
    def LShr(a, b) -> Value:
        return not_implemented()

    ### Relational operators
    # we provide also default implementations
    @staticmethod
    def Le(a: Value, b: Value, unsigned: bool = False) -> Value:
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        return ConcreteBool(bool(a.unwrap() <= b.unwrap()))

    @staticmethod
    def Lt(a, b, unsigned: bool = False) -> Value:
        return ConcreteBool(bool(a.unwrap() < b.unwrap()))

    @staticmethod
    def Ge(a, b, unsigned: bool = False) -> Value:
        return ConcreteBool(bool(a.unwrap() >= b.unwrap()))

    @staticmethod
    def Gt(a, b, unsigned: bool = False) -> Value:
        return ConcreteBool(bool(a.unwrap() > b.unwrap()))

    @staticmethod
    def Eq(a, b, unsigned: bool = False) -> Value:
        return ConcreteBool(bool(a.unwrap() == b.unwrap()))

    @staticmethod
    def Ne(a, b, unsigned: bool = False) -> Value:
        return ConcreteBool(bool(a.unwrap() != b.unwrap()))

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Value, b: Value) -> Value:
        assert isinstance(a, cls), a
        assert isinstance(b, cls), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.bitwidth()
        assert bw == b.bitwidth(), f"{a.bitwidth()} != {b.bitwidth()}"
        return ConcreteFloat(a.unwrap() + b.unwrap(), bw)

    @staticmethod
    def Sub(a, b) -> Value:
        return not_implemented()

    @staticmethod
    def Mul(a, b) -> Value:
        return not_implemented()

    @staticmethod
    def Div(a, b, unsigned: bool = False) -> Value:
        return not_implemented()

    @staticmethod
    def Rem(a, b, unsigned: bool = False) -> Value:
        return not_implemented()

    @staticmethod
    def Abs(a) -> Value:
        return not_implemented()

    @staticmethod
    def Neg(a) -> Value:
        return not_implemented()

    @staticmethod
    def FpOp(op, val) -> Value:
        return not_implemented()
