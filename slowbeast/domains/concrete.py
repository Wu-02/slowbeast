from slowbeast.ir.types import IntType, BoolType, Type, PointerType
from slowbeast.ir.value import Value


def getUnsigned(a):
    """ Get unsigned value for signed in 2's complement """
    x = a.value()
    if x >= 0:
        return x
    return x + (1 << a.bitwidth())


def wrap_to_bw(x, bw):
    m = 1 << bw
    if x >= 0:
        while x >= m:
            x -= m
    else:
        m = m
        while x <= -m:
            x += m
    return x


class ConcreteVal(Value):
    """
    Integer constant or boolean
    """

    __slots__ = ["_value"]

    def __init__(self, c, ty):
        assert isinstance(c, (int, bool)), f"Invalid constant: {c} {type(c)}"
        assert isinstance(ty, Type), f"Invalid type: {ty}"
        assert not isinstance(ty, PointerType), f"Invalid type: {ty}"
        super().__init__(ty)
        self._value = c

        assert not self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool() or (c in (True, False)), "Invalid boolean constant"
        assert self.is_bool() or isinstance(c, int)

    def as_value(self):
        return "{0}:{1}".format(str(self._value), self.type())

    def value(self):
        return self._value

    def is_concrete(self):
        return True

    def __repr__(self):
        return f"{self._value}:{self.type()}"

    def __hash__(self):
        return self._value

    def __eq__(self, rhs):
        assert isinstance(rhs, ConcreteVal)
        return self.value() == rhs.value() and self.type() == rhs.type()

class ConcreteDomain:
    """
    Takes care of handling concrete computations.
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            assert isinstance(a, Value), a
            if not a.is_concrete():
                return False
        return True

    def Value(c, bw):
        if isinstance(c, bool):
            assert bw == 1
            return ConcreteVal(c, BoolType())
        return ConcreteVal(c, IntType(bw))

    def getTrue():
        return ConcreteVal(True, BoolType())

    def getFalse():
        return ConcreteVal(False, BoolType())

    def conjunction(*args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteVal(all(map(lambda x: x.value() is True, args)), BoolType())

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteVal(any(map(lambda x: x.value() is True, args)), BoolType())

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return ConcreteVal(a.value() and b.value(), BoolType())
        else:
            return ConcreteVal(a.value() & b.value(), a.type())

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return ConcreteVal(a.value() or b.value(), BoolType())
        else:
            return ConcreteVal(a.value() | b.value(), a.type())

    def Xor(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        return ConcreteVal(a.value() ^ b.value(), a.type())

    def Not(a):
        assert ConcreteDomain.belongto(a)
        if a.is_bool():
            return ConcreteVal(not a.value(), BoolType())
        else:
            return ConcreteVal(~a.value(), a.type())

    def ZExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        return ConcreteVal(getUnsigned(a), IntType(b.value()))

    def SExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        sb = 1 << (b.value() - 1)
        val = (a.value() & (sb - 1)) - (a.value() & sb)
        return ConcreteVal(val, IntType(b.value()))

    def Shl(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ConcreteVal(a.value() << b.value(), a.type())

    def AShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ConcreteVal(a.value() >> b.value(), a.type())

    def LShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = a.value()
        return ConcreteVal(
            a.value() >> b.value()
            if val >= 0
            else (val + (1 << a.bitwidth())) >> b.value(),
            a.type(),
        )

    def Extract(a, start, end):
        assert ConcreteDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        bitsnum = end.value() - start.value() + 1
        return ConcreteVal(
            (a.value() >> start.value()) & ((1 << (bitsnum)) - 1), IntType(bitsnum)
        )

    def Rem(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() != 0, "Invalid remainder"
        if unsigned:
            return ConcreteVal(getUnsigned(a) % getUnsigned(b), a.type())
        return ConcreteVal(a.value() % b.value(), a.type())

    ##
    # Relational operators
    def Le(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) <= getUnsigned(b), BoolType())
        return ConcreteVal(a.value() <= b.value(), BoolType())

    def Lt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) < getUnsigned(b), BoolType())
        return ConcreteVal(a.value() < b.value(), BoolType())

    def Ge(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) >= getUnsigned(b), BoolType())
        return ConcreteVal(a.value() >= b.value(), BoolType())

    def Gt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) > getUnsigned(b), BoolType())
        return ConcreteVal(a.value() > b.value(), BoolType())

    def Eq(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) == getUnsigned(b), BoolType())
        return ConcreteVal(a.value() == b.value(), BoolType())

    def Ne(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return ConcreteVal(getUnsigned(a) != getUnsigned(b), BoolType())
        return ConcreteVal(a.value() != b.value(), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() + b.value(), bw), a.type())

    def Sub(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() - b.value(), bw), a.type())

    def Mul(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() * b.value(), bw), a.type())

    def Div(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        result_ty = a.type()
        if unsigned:
            return ConcreteVal(getUnsigned(a) / getUnsigned(b), result_ty)
        return ConcreteVal(
            wrap_to_bw(int(a.value() / b.value()), result_ty.bitwidth()), result_ty
        )
