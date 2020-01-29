from .. ir.types import Type
from .. ir.value import Value, Constant


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

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() and b.getValue(), Type(1))

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() or b.getValue(), Type(1))

    def Not(a):
        assert ConcreteDomain.belongto(a)
        return Constant(not a.getValue(), Type(1))

    ##
    # Relational operators
    def Le(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() <= b.getValue(), Type(1))

    def Lt(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() < b.getValue(), Type(1))

    def Ge(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() >= b.getValue(), Type(1))

    def Gt(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() > b.getValue(), Type(1))

    def Eq(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() == b.getValue(), Type(1))

    def Ne(a, b):
        assert ConcreteDomain.belongto(a, b)
        return Constant(a.getValue() != b.getValue(), Type(1))

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
