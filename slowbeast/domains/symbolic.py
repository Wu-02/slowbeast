from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import Type, IntType, BoolType

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
    from z3 import is_bv, is_bv_value, is_bool, is_and, is_or, is_not
    from z3 import (
        is_app_of,
        Z3_OP_SLEQ,
        Z3_OP_SLT,
        Z3_OP_SGEQ,
        Z3_OP_SGT,
        Z3_OP_ULT,
        Z3_OP_ULEQ,
        Z3_OP_UGT,
        Z3_OP_UGEQ,
        Z3_OP_EQ,
    )
    from z3 import is_true, is_false
    from z3 import simplify, substitute
    from z3 import Goal, Tactic

    try:
        from z3 import asIEEEBV, fromIEEEBV
    except ImportError:

        def asIEEEBV(x):
            return None

        def fromIEEEBV(x):
            return None

    def eliminate_common_subexpr(expr):
        # XXX: not efficient, it is rather
        # to prettify expressions while debugging
        if is_and(expr):
            subexp = [eliminate_common_subexpr(c) for c in expr.children()]
            n = 0
            for idx in range(0, len(subexp)):
                c = subexp[idx]
                subs = [(s, BoolVal(True)) for (i, s) in enumerate(subexp) if i != n]
                subexp[idx] = simplify(substitute(c, *subs))
                n += 1
            return And(*subexp)
        elif is_or(expr):
            return Or(*(eliminate_common_subexpr(c) for c in expr.children()))
        elif is_not(expr):
            return Not(*(eliminate_common_subexpr(c) for c in expr.children()))
        else:
            return expr

    def TRUE():
        return BoolVal(True)

    def FALSE():
        return BoolVal(False)

    def bv(name, bw):
        return BitVec(name, bw)

    def bv_const(v, bw):
        return BitVecVal(v, bw)

    def castToBV(b):
        if not b.is_bool():
            return b.unwrap()
        return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))

    def castToBool(b):
        if b.is_bool():
            return b.unwrap()
        return If(b.unwrap() != bv_const(0, b.bitwidth()), TRUE(), FALSE())

    def bv_size(bw):
        return bw.sort().size()

    def subexpressions(expr):
        children = expr.children()
        for c in children:
            yield from subexpressions(c)
        yield expr

    def to_cnf(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Tactic("tseitin-cnf")
        return t(g)[0]

    def solver_to_sb_type(s):
        if is_bv(s):
            return IntType(s.sort().size())
        assert is_bool(s), "Unhandled expression"
        return BoolType()


else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.shortcuts import BVULT, BVULE, BVUGT, BVUGE
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

    __slots__ = ["_expr"]

    def __init__(self, e, t):
        assert not isinstance(e, int), e
        assert isinstance(t, Type), t
        Value.__init__(self, t)
        self._expr = e

    def unwrap(self):
        return self._expr

    def isNondetLoad(self):
        return False

    def name(self):
        return str(self._expr)

    def is_concrete(self):
        return False

    def as_value(self):
        return str(self)

    def subexpressions(self):
        """ Traverse the expression and return its all subexpressions """
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in subexpressions(self.unwrap())
        )

    def children(self):
        """
        Get the children (1st-level subexpressions) of this expression.
        E.g. for And(a, b) this method returns [a, b].
        """
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in self.unwrap().children()
        )

    def to_cnf(self):
        """
        Get the expression in CNF form.
        """
        return Expr(And(*to_cnf(self.unwrap())), self.type())

    def isAnd(self):
        return is_and(self.unwrap())

    def isOr(self):
        return is_or(self.unwrap())

    def isNot(self):
        return is_not(self.unwrap())

    def isEq(self):
        return is_app_of(self._expr, Z3_OP_EQ)

    def isLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ) or is_app_of(self._expr, Z3_OP_ULEQ)

    def isGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ) or is_app_of(self._expr, Z3_OP_UGEQ)

    def isLt(self):
        return is_app_of(self._expr, Z3_OP_SLT) or is_app_of(self._expr, Z3_OP_ULT)

    def isGt(self):
        return is_app_of(self._expr, Z3_OP_SGT) or is_app_of(self._expr, Z3_OP_UGT)

    def isSLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ)

    def isSGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ)

    def isSLt(self):
        return is_app_of(self._expr, Z3_OP_SLT)

    def isSGt(self):
        return is_app_of(self._expr, Z3_OP_SGT)

    def isULe(self):
        return is_app_of(self._expr, Z3_OP_ULEQ)

    def isUGe(self):
        return is_app_of(self._expr, Z3_OP_UGEQ)

    def isULt(self):
        return is_app_of(self._expr, Z3_OP_ULT)

    def isUGt(self):
        return is_app_of(self._expr, Z3_OP_UGT)

    def __hash__(self):
        return self._expr.__hash__()

    def __eq__(self, rhs):
        return self._expr == rhs._expr

    def __repr__(self):
        return "<{0}:{1}>".format(self._expr, self.type())


class NondetLoad(Expr):
    __slots__ = ["load", "alloc"]

    def __init__(self, e, t, load, alloc):
        super(NondetLoad, self).__init__(e, t)
        self.load = load
        self.alloc = alloc

    def isNondetLoad(self):
        return True

    def fromExpr(expr, load, alloc):
        assert isinstance(expr, Expr)
        return NondetLoad(expr.unwrap(), expr.type(), load, alloc)

    def __repr__(self):
        return f"L({self.alloc.as_value()})={Expr.__repr__(self)}"


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

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), BoolType())
            return Expr(bv_const(v.value(), v.type().bitwidth()), v.type())

        raise NotImplementedError("Invalid value for lifting: {0}".format(v))

    def simplify(expr):
        return Expr(
            simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.type()
        )

    def substitute(expr, *what):
        return Expr(
            substitute(expr.unwrap(), *((a.unwrap(), b.unwrap()) for (a, b) in what)),
            expr.type(),
        )

    def pythonConstant(expr):
        """Take a symbolic constant and get a python constant for it.
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
        return Expr(bv(name, bw), IntType(bw))

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
    def conjunction(*args):
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(And(*map(lambda x: x.unwrap(), args)), BoolType())

    def disjunction(*args):
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(Or(*map(lambda x: x.unwrap(), args)), BoolType())

    def And(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() & b.unwrap(), a.type())

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() | b.unwrap(), a.type())

    def Xor(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type()
        if a.is_bool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(a.unwrap() ^ b.unwrap(), a.type())

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_bool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~a.unwrap(), a.type())

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        assert a.bitwidth() <= b.value(), "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        return Expr(BVZExt(b.value() - a.bitwidth(), castToBV(a)), IntType(b.value()))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        return Expr(BVSExt(b.value() - a.bitwidth(), castToBV(a)), IntType(b.value()))

    def Cast(a: Value, ty: Type):
        """ Reinterpret cast """
        assert BVSymbolicDomain.belongto(a)
        v = a.unwrap()
        if a.is_int() and ty.is_float():
            e = asIEEEBV(v)
            if e:
                return Expr(e, ty)
        elif a.is_float() and ty.is_int():
            e = fromIEEEBV(v)
            if e:
                return Expr(e, ty)
        return None  # unsupported conversion

    def Extract(a, start, end):
        assert BVSymbolicDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        return Expr(
            BVExtract(end.value(), start.value(), a.unwrap()),
            IntType(end.value() - start.value() + 1),
        )

    def Shl(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() << b.unwrap(), a.type())

    def AShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(a.unwrap() >> b.unwrap(), a.type())

    def LShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        return Expr(BVLShR(a.unwrap(), b.unwrap()), a.type())

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
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        return Expr(a.unwrap() + b.unwrap(), result_ty)

    def Sub(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        return Expr(a.unwrap() - b.unwrap(), result_ty)

    def Mul(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        return Expr(a.unwrap() * b.unwrap(), result_ty)

    def Div(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(UDiv(a.unwrap(), b.unwrap()), result_ty)
        return Expr(a.unwrap() / b.unwrap(), result_ty)

    def Rem(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
