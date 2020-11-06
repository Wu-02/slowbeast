from ..ir.types import Type, BoolType
from ..ir.value import Value, Constant


def getUnsigned(a):
    """ Get unsigned value for signed in 2's complement """
    x = a.getValue()
    if x >= 0:
        return x
    return x + (1 << a.getBitWidth())


class ConcreteDomain:
    """
    Takes care of handling concrete computations.
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            assert isinstance(a, Value), a
            if not a.isConstant():
                return False
        return True

    def Constant(c, bw):
        if isinstance(c, bool):
            assertbw == 1
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
        assert all(map(lambda a: a.isBool(), args))
        return Constant(all(args), BoolType())

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.isBool(), args))
        return Constant(any(args), BoolType())

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        if a.isBool():
            return Constant(a.getValue() and b.getValue(), BoolType())
        else:
            return Constant(a.getValue() & b.getValue(), a.getType())

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        if a.isBool():
            return Constant(a.getValue() or b.getValue(), BoolType())
        else:
            return Constant(a.getValue() | b.getValue(), a.getType())

    def Xor(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        return Constant(a.getValue() ^ b.getValue(), a.getType())

    def Not(a):
        assert ConcreteDomain.belongto(a)
        if a.isBool():
            return Constant(not a.getValue(), BoolType())
        else:
            return Constant(~a.getValue(), a.getType())

    def ZExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getBitWidth() < b.getValue(), "Invalid zext argument"
        return Constant(getUnsigned(a), Type(b.getValue()))

    def SExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getBitWidth() <= b.getValue(), "Invalid sext argument"
        sb = 1 << (b.getValue() - 1)
        val = (a.getValue() & (sb - 1)) - (a.getValue() & sb)
        return Constant(val, Type(b.getValue()))

    def Shl(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.getValue() < a.getBitWidth(), "Invalid shift"
        return Constant(a.getValue() << b.getValue(), a.getType())

    def AShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.getValue() < a.getBitWidth(), "Invalid shift"
        return Constant(a.getValue() >> b.getValue(), a.getType())

    def LShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.getValue() < a.getBitWidth(), "Invalid shift"
        val = a.getValue()
        return Constant(
            a.getValue() >> b.getValue()
            if val >= 0
            else (val + (1 << a.getBitWidth())) >> b.getValue(),
            a.getType(),
        )

    def Extract(a, start, end):
        assert ConcreteDomain.belongto(a)
        assert start.isConstant()
        assert end.isConstant()
        bitsnum = end.getValue() - start.getValue() + 1
        return Constant(
            (a.getValue() >> start.getValue()) & ((1 << (bitsnum)) - 1), Type(bitsnum)
        )

    def Rem(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        assert b.getValue() != 0, "Invalid remainder"
        if unsigned:
            return Constant(getUnsigned(a) % getUnsigned(b), a.getType())
        return Constant(a.getValue() % b.getValue(), a.getType())

    ##
    # Relational operators
    def Le(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) <= getUnsigned(b), BoolType())
        return Constant(a.getValue() <= b.getValue(), BoolType())

    def Lt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) < getUnsigned(b), BoolType())
        return Constant(a.getValue() < b.getValue(), BoolType())

    def Ge(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) >= getUnsigned(b), BoolType())
        return Constant(a.getValue() >= b.getValue(), BoolType())

    def Gt(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) > getUnsigned(b), BoolType())
        return Constant(a.getValue() > b.getValue(), BoolType())

    def Eq(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) == getUnsigned(b), BoolType())
        return Constant(a.getValue() == b.getValue(), BoolType())

    def Ne(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        if unsigned:
            return Constant(getUnsigned(a) != getUnsigned(b), BoolType())
        return Constant(a.getValue() != b.getValue(), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        return Constant(a.getValue() + b.getValue(), a.getType())

    def Sub(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        return Constant(a.getValue() - b.getValue(), a.getType())

    def Mul(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getType() == b.getType()
        return Constant(a.getValue() * b.getValue(), a.getType())

    def Div(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        result_ty = a.getType()
        if unsigned:
            return Constant(
                getUnsigned(a.getValue()) / getUnsigned(b.getValue()), result_ty
            )
        return Constant(int(a.getValue() / b.getValue()), result_ty)
