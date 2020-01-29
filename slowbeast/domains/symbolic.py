from .. ir.value import Value, Constant
from .. ir.types import Type
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
        Value.__init__(self, t.getBitWidth(), isptr=False)
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
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(And(a._expr, b._expr), Type(1))

    def Or(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(Or(a._expr, b._expr), Type(1))

    def Not(a):
        assert isinstance(a, Expr)
        return Expr(Not(a._expr), Type(1))

    def getTrue():
        return Expr(TRUE(), Type(1))

    def getFalse():
        return Expr(FALSE(), Type(1))

    ##
    # Relational operators

    def Le(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr <= b._expr, Type(1))

    def Lt(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr < b._expr, Type(1))

    def Ge(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr >= b._expr, Type(1))

    def Gt(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr > b._expr, Type(1))

    def Eq(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr == b._expr, Type(1))

    def Ne(a, b):
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr != b._expr, Type(1))

    ##
    # Arithmetic operations


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
