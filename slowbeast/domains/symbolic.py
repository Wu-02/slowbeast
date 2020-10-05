from .. ir.value import Value, Constant
from .. ir.types import Type, BoolType

_use_z3 = True
if _use_z3:
    from z3 import If, Or, And, Xor, Not, BoolVal, BitVec, BitVecVal, URem, SRem, UDiv
    from z3 import ULT as BVULT
    from z3 import ULE as BVULE
    from z3 import UGT as BVUGT
    from z3 import UGE as BVUGE
    from z3 import ZeroExt as BVZExt
    from z3 import SignExt as BVSExt
    from z3 import Extract as BVExtract
    from z3 import LShR as BVLShR
    from z3 import is_bv, is_bv_value, is_bool
    from z3 import is_true, is_false
    from z3 import simplify, substitute

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
            return b.unwrap()
        return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))

    def castToBool(b):
        if b.isBool():
            return b.unwrap()
        return If(b.unwrap() != bv_const(0, b.getBitWidth()), TRUE(), FALSE())

    def bv_size(bw):
        return bw.sort().size()

    def subexpressions(expr):
        children = expr.children()
        for c in children:
            yield from subexpressions(c)
        yield expr

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

    __slots__ = ['_expr']

    def __init__(self, e, t):
        assert not isinstance(e, int)
        assert isinstance(t, Type)
        Value.__init__(self, t)
        self._expr = e

    def unwrap(self):
        return self._expr

    def isNondetLoad(self):
        return False

    def name(self):
        return str(self._expr)

    def asValue(self):
        return str(self)

    def symbols(self):
        """
        Traverse the expression and return symbols
        from this expression (constants are not symbols)
        """
        return [Expr(e, Type(bv_size(e))) for e in exprsymbols(self._expr)]

    def subexpressions(self):
        """ Traverse the expression and return it all subexpressions """
        def get_type(s):
            if is_bv(s):
                return Type(s.sort().size())
            assert is_bool(s), "Unhandled expression"
            return BoolType()

        return (Expr(s, get_type(s))
                for s in subexpressions(self.unwrap()))

    def __hash__(self):
        return self._expr.__hash__()

    def __eq__(self, rhs):
        return self._expr == rhs._expr

    def __repr__(self):
        return "<{0}:{1}>".format(self._expr, self.getType())

class NondetLoad(Expr):
    __slots__ = ['load', 'alloc']

    def __init__(self, e, t, load, alloc):
        super(NondetLoad, self).__init__(e,  t)
        self.load = load
        self.alloc = alloc

    def isNondetLoad(self):
        return True

    def fromExpr(expr, load, alloc):
        assert isinstance(expr, Expr)
        return NondetLoad(expr.unwrap(), expr.getType(), load, alloc)

    def __repr__(self):
        return f"L({self.alloc.asValue()})={Expr.__repr__(self)}"

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

    def simplify(expr, *assumptions):
        return Expr(simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.getType())

    def substitute(expr, *what):
        return Expr(substitute(expr.unwrap(),
                    *((a.unwrap(), b.unwrap()) for (a, b) in what)), expr.getType())

    def pythonConstant(expr):
        """ Take a symbolic constant and get a python constant for it.
            Return None if the given expression is not a constant number
            or boolean
        """
        val = expr.unwrap()
        if is_bv_value(val):
            return val.as_long()
        elif is_true(val):
            return True
        elif is_false(val):
            return False

        return None

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
        assert a.getType() == b.getType()
        if a.isBool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() & b.unwrap(), a.getType())

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType()
        if a.isBool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() | b.unwrap(), a.getType())

    def Xor(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType()
        if a.isBool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() ^ b.unwrap(), a.getType())

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        if a.isBool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~a.unwrap(), a.getType())

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.isConstant()
        assert a.getBitWidth() <= b.getValue(), "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        return Expr(
            BVZExt(
                b.getValue() -
                a.getBitWidth(),
                castToBV(a)),
            Type(
                b.getValue()))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.isConstant()
        assert a.getBitWidth() <= b.getValue(), "Invalid sext argument"
        return Expr(
            BVSExt(
                b.getValue() -
                a.getBitWidth(),
                castToBV(a)),
            Type(
                b.getValue()))

    def Extract(a, start, end):
        assert BVSymbolicDomain.belongto(a)
        assert start.isConstant()
        assert end.isConstant()
        return Expr(BVExtract(end.getValue(), start.getValue(), a.unwrap()),
                    Type(end.getValue() - start.getValue() + 1))

    def Shl(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() << b.unwrap(), a.getType())

    def AShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() >> b.unwrap(), a.getType())

    def LShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(BVLShR(a.unwrap(), b.unwrap()), a.getType())

    def getTrue():
        return Expr(TRUE(), BoolType())

    def getFalse():
        return Expr(FALSE(), BoolType())

    ##
    # Relational operators

    def Le(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVULE(a.unwrap(), b.unwrap()), BoolType())
        return Expr(a.unwrap() <= b.unwrap(), BoolType())

    def Lt(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVULT(a.unwrap(), b.unwrap()), BoolType())
        return Expr(a.unwrap() < b.unwrap(), BoolType())

    def Ge(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVUGE(a.unwrap(), b.unwrap()), BoolType())
        return Expr(a.unwrap() >= b.unwrap(), BoolType())

    def Gt(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        if unsigned:
            return Expr(BVUGT(a.unwrap(), b.unwrap()), BoolType())
        return Expr(a.unwrap() > b.unwrap(), BoolType())

    def Eq(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() == b.unwrap(), BoolType())

    def Ne(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() != b.unwrap(), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a.unwrap() + b.unwrap(), result_ty)

    def Sub(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a.unwrap() - b.unwrap(), result_ty)

    def Mul(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        return Expr(a.unwrap() * b.unwrap(), result_ty)

    def Div(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        if unsigned:
            return Expr(UDiv(a.unwrap(), b.unwrap()), result_ty)
        return Expr(a.unwrap() / b.unwrap(), result_ty)

    def Rem(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.getType() == b.getType(),\
            "Operation on invalid types: {0} != {1}".format(
            a.getType(), b.getType())
        result_ty = a.getType()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
