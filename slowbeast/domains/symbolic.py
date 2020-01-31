from .. ir.value import Value, Constant
from .. ir.types import Type, BoolType

_use_z3 = True
if _use_z3:
    from z3 import If, Or, And, Not, BoolVal, BitVec, BitVecVal
    from z3 import ULT as BVULT
    from z3 import ULE as BVULE
    from z3 import UGT as BVUGT
    from z3 import UGE as BVUGE
    from z3 import ZeroExt as BVZExt
    from z3 import SignExt as BVSExt

    def TRUE():
        return BoolVal(True)

    def FALSE():
        return BoolVal(False)

    def bv(name, bw):
        return BitVec(name, bw)

    def bv_const(v, bw):
        return BitVecVal(v, bw)

    def castToBV(b):
        if not b.isBool():
            return b._expr
        return If(b._expr, bv_const(1, 1), bv_const(0, 1))

else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.shortcuts import BVULT, BVULE, BVUGT, BVUGE
    from pysmt.shortcuts import BVZext, BVSext
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
        assert not isinstance(e, int)
        assert isinstance(t, Type)
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

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.isConstant()
        assert a.getBitWidth() <= b.getValue(), "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        return Expr(BVZExt(b.getValue() - a.getBitWidth(), castToBV(a)), Type(b.getValue()))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.isConstant()
        assert a.getBitWidth() <= b.getValue(), "Invalid sext argument"
        return Expr(BVSExt(b.getValue() - a.getBitWidth(), castToBV(a)), Type(b.getValue()))


    def getTrue():
        return Expr(TRUE(), BoolType())

    def getFalse():
        return Expr(FALSE(), BoolType())

    ##
    # Relational operators

    def Le(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVULE(a._expr, b._expr), BoolType())
        return Expr(a._expr <= b._expr, BoolType())

    def Lt(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVULT(a._expr, b._expr), BoolType())
        return Expr(a._expr < b._expr, BoolType())

    def Ge(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVUGE(a._expr, b._expr), BoolType())
        return Expr(a._expr >= b._expr, BoolType())

    def Gt(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVUGT(a._expr, b._expr), BoolType())
        return Expr(a._expr > b._expr, BoolType())

    def Eq(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a._expr == b._expr, BoolType())

    def Ne(a, b, unsigned = False):
        assert BVSymbolicDomain.belongto(a, b)
        print(a._expr, b._expr, unsigned)
        print(a._expr.sort(), b._expr.sort())
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
