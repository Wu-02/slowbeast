from .. ir.value import Value, Constant
from .. ir.types import Type, BoolType
_use_z3 = True
if _use_z3:
    from z3 import Or, And, Not, BoolVal, BitVec, BitVecVal

    def TRUE():
        return BoolVal(True)

    def FALSE():
        return BoolVal(False)

    def bv(name, bw):
        return BitVec(name, bw)

    def bv_const(v, bw):
        return BitVecVal(v, bw)
else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.typing import BVType

    def bv(name, bw):
        return Symbol(name, BVType(bw))

    def bv_const(v, bw):
        return BV(v, bw)


class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """

    def __init__(self, e, t):
        Value.__init__(self, t)
        self._expr = e

    def asValue(self):
        return str(self)

    def __repr__(self):
        return "<{0}:{1}>".format(self._expr, self.getType())


class BVSymbolicDomain:
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if not isinstance(a, Expr):
                return False
        return True

    def lift(v):
        assert isinstance(v, Value), "Invalid value for lifting: {0}".format(v)
        if isinstance(v, Expr):
            return v

        if v.isConstant():
            return Expr(
                bv_const(
                    v.getValue(),
                    v.getType().getBitWidth()),
                v.getType())

        raise NotImplementedError("Invalid value for lifting: {0}".format(v))

    def Constant(c, bw):
        return bv_const(c, bw)

    ##
    # variables
    def Var(name, bw=64):
        return Expr(bv(name, bw), Type(bw))

    def Int1(name):
        return BVSymbolicDomain.Var(name, 1)

    def Int8(name):
        return BVSymbolicDomain.Var(name, 8)

    def Int16(name):
        return BVSymbolicDomain.Var(name, 16)

    def Int32(name):
        return BVSymbolicDomain.Var(name, 32)

    def Int64(name):
        return BVSymbolicDomain.Var(name, 64)

    ##
    # Logic operators
    def And(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(And(a._expr, b._expr), BoolType())

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(Or(a._expr, b._expr), BoolType())

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        return Expr(Not(a._expr), BoolType())

    def getTrue():
        return Expr(TRUE(), BoolType())

    def getFalse():
        return Expr(FALSE(), BoolType())

    ##
    # Relational operators

    def Le(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr <= b._expr, BoolType())

    def Lt(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr < b._expr, BoolType())

    def Ge(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr >= b._expr, BoolType())

    def Gt(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr > b._expr, BoolType())

    def Eq(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr == b._expr, BoolType())

    def Ne(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr != b._expr, BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a._expr + b._expr, result_ty)

    def Sub(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a._expr - b._expr, result_ty)

    def Mul(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a._expr * b._expr, result_ty)

    def Div(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a._expr / b._expr, result_ty)


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
