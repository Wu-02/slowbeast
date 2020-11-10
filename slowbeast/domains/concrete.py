from ..ir.types import Type, BoolType
from ..ir.value import Value, Constant


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

    def Constant(c, bw):
        if isinstance(c, bool):
            assert bw == 1
            return Constant(c, BoolType())
        return Constant(c, Type(bw))

    def getTrue():
        return Constant(True, BoolType())

    def getFalse():
        return Constant(False, BoolType())

    def conjunction(*args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return Constant(all(map(lambda x: x.value() is True, args)), BoolType())

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return Constant(any(map(lambda x: x.value() is True, args)), BoolType())

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return Constant(a.value() and b.value(), BoolType())
        else:
            return Constant(a.value() & b.value(), a.type())

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return Constant(a.value() or b.value(), BoolType())
        else:
            return Constant(a.value() | b.value(), a.type())

    def Xor(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type()
        return Constant(a.value() ^ b.value(), a.type())

    def Not(a):
        assert ConcreteDomain.belongto(a)
        if a.is_bool():
            return Constant(not a.value(), BoolType())
        else:
            return Constant(~a.value(), a.type())

    def ZExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        return Constant(getUnsigned(a), Type(b.value()))

    def SExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        sb = 1 << (b.value() - 1)
        val = (a.value() & (sb - 1)) - (a.value() & sb)
        return Constant(val, Type(b.value()))

    def Shl(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return Constant(a.value() << b.value(), a.type())

    def AShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return Constant(a.value() >> b.value(), a.type())

    def LShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = a.value()
        return Constant(
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
        return Constant(
            (a.value() >> start.value()) & ((1 << (bitsnum)) - 1), Type(bitsnum)
        )

    def Rem(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() != 0, "Invalid remainder"
        if unsigned:
            return Constant(getUnsigned(a) % getUnsigned(b), a.type())
        return Constant(a.value() % b.value(), a.type())

    ##
    # Relational operators
    def Le(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) <= getUnsigned(b), BoolType())
        return Constant(a.value() <= b.value(), BoolType())

    def Lt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) < getUnsigned(b), BoolType())
        return Constant(a.value() < b.value(), BoolType())

    def Ge(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) >= getUnsigned(b), BoolType())
        return Constant(a.value() >= b.value(), BoolType())

    def Gt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) > getUnsigned(b), BoolType())
        return Constant(a.value() > b.value(), BoolType())

    def Eq(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) == getUnsigned(b), BoolType())
        return Constant(a.value() == b.value(), BoolType())

    def Ne(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) != getUnsigned(b), BoolType())
        return Constant(a.value() != b.value(), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return Constant(wrap_to_bw(a.value() + b.value(), bw), a.type())

    def Sub(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return Constant(wrap_to_bw(a.value() - b.value(), bw), a.type())

    def Mul(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        bw = a.type().bitwidth()
        return Constant(wrap_to_bw(a.value() * b.value(), bw), a.type())

    def Div(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        result_ty = a.type()
        if unsigned:
            return Constant(getUnsigned(a) / getUnsigned(b), result_ty)
        return Constant(
            wrap_to_bw(int(a.value() / b.value()), result_ty.bitwidth()), result_ty
        )
