from .. ir.types import Type, BoolType
from .. ir.value import Value, Constant


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
            assert isinstance(a, Value)
            if not a.isConstant():
                return False
        return True

    def Constant(c, bw):
        if isinstance(c, bool):
            assertbw == 1
            return Constant(c, BoolType())
        return Constant(c, Type(bw))

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() and b.getValue(), BoolType())

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() or b.getValue(), BoolType())

    def Not(a):
        assert ConcreteDomain.belongto(a)
        return Constant(not a.getValue(), BoolType())

    def ZExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getBitWidth() <= b.getValue(), "Invalid zext argument"
        return Constant(a.getValue(), Type(b.getValue()))

    def SExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.getBitWidth() <= b.getValue(), "Invalid sext argument"
        sb = 1 << (b.getValue() - 1)
        val = (a.getValue() & (sb - 1)) - (a.getValue() & sb)
        return Constant(val, Type(b.getValue()))

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
        result_ty = Type(max(a.getType().getBitWidth(),
                             b.getType().getBitWidth()))
        return Constant(a.getValue() + b.getValue(), result_ty)

    def Sub(a, b):
        assert ConcreteDomain.belongto(a, b)
        result_ty = Type(max(a.getType().getBitWidth(),
                             b.getType().getBitWidth()))
        return Constant(a.getValue() - b.getValue(), result_ty)

    def Mul(a, b):
        assert ConcreteDomain.belongto(a, b)
        result_ty = Type(2 * max(a.getType().getBitWidth(),
                                 b.getType().getBitWidth()))
        return Constant(a.getValue() * b.getValue(), result_ty)

    def Div(a, b):
        assert ConcreteDomain.belongto(a, b)
        result_ty = Type(max(a.getType().getBitWidth(),
                             b.getType().getBitWidth()))
        return Constant(a.getValue() / b.getValue(), result_ty)
