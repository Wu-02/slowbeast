from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import Type, IntType, BoolType, FloatType
from slowbeast.ir.instruction import FpOp

_use_z3 = True
if _use_z3:
    from z3 import (
        If,
        Or,
        And,
        Xor,
        Not,
        Bool,
        BoolVal,
        BitVec,
        BitVecVal,
        BitVecSort,
        URem,
        SRem,
        UDiv,
        ULT as BVULT,
        ULE as BVULE,
        UGT as BVUGT,
        UGE as BVUGE,
        ZeroExt as BVZExt,
        SignExt as BVSExt,
        Extract as BVExtract,
        Concat as BVConcat,
        LShR as BVLShR,
    )
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
    from z3 import is_true, is_false, simplify, substitute
    from z3 import Goal, Tactic
    from z3 import (
        FP,
        Float32,
        Float64,
        Float128,
        FPVal,
        fpAbs,
        fpNeg,
        fpIsInf,
        fpIsNaN,
        fpToFP,
        fpFPToFP,
        fpBVToFP,
        fpToIEEEBV,
        RNE,
        fpToUBV,
        fpToSBV,
        fpEQ,
        fpNEQ,
        fpGEQ,
        fpGT,
        fpLEQ,
        fpLT,
    )

    def trunc_fp(fexpr, bw):
        return simplify(fpFPToFP(RNE(), fexpr, get_fp_sort(bw)))

    def to_double(x):
        bw = x.bitwidth()
        if x.is_float() and bw == 64:
            return x._expr
        # we first must convert to float and then extend to double
        if x.is_float() and bw == 32:
            r = x._expr
        else:
            r = simplify(fpToFP(x._expr, get_fp_sort(bw)))
        r = simplify(fpFPToFP(RNE(), r, Float64()))
        return r

    def to_bv(x):
        if x.is_float():
            return simplify(fpToIEEEBV(x._expr))

        return x.unwrap()

    def floatToUBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

    def floatToSBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

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

    def boolToBV(b):
        if not b.is_bool():
            return b.unwrap()
        return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))

    def castToFP(b):
        if b.is_float():
            return b.unwrap()
        return fpToFP(b.unwrap(), get_fp_sort(b.type().bitwidth()))

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

    def get_fp_sort(bw):
        if bw == 32:
            return Float32()
        if bw == 64:
            return Float64()
        elif bw == 128:
            return Float128()
        raise NotImplementedError("Invalid FP type")


else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.shortcuts import BVULT, BVULE, BVUGT, BVUGE
    from pysmt.typing import BVType

    def bv(name, bw):
        return Symbol(name, BVType(bw))

    def bv_const(v, bw):
        return BV(v, bw)


def dom_is_symbolic(v):
    return v.KIND == 2


class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """

    # FIXME: get rid of the magic constant
    KIND = 2

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

    def is_future(self):
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


class Future(Expr):
    """
    Represents a value of non-executed operation (instruction)
    (that is going to be executed as a feedback to the developement of the search
    """

    __slots__ = "_instr", "_state"

    def __init__(self, e, t, instr, state):
        super().__init__(e, t)
        # to which instr we assigned the nondet value
        self._instr = instr
        # stored state
        self._state = state

    def is_future(self):
        return True

    def state(self):
        return self._state

    def from_expr(expr, instr, state):
        assert isinstance(expr, Expr)
        return Future(expr.unwrap(), expr.type(), instr)

    def __repr__(self):
        return f"future({self._instr.as_value()})={super().__repr__()}"


def zext_expr(a, bw):
    return BVZExt(bw - a.bitwidth(), boolToBV(a))


def sext_expr(a, bw):
    return BVSExt(bw - a.bitwidth(), boolToBV(a))


class BVSymbolicDomain:
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if a.KIND != 2:
                return False
        return True

    def lift(v):
        assert isinstance(v, Value), "Invalid value for lifting: {0}".format(v)
        if isinstance(v, Expr):
            return v

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), BoolType())
            ty = v.type()
            if v.is_float():
                return Expr(FPVal(v.value(), get_fp_sort(ty.bitwidth())), ty)
            return Expr(bv_const(v.value(), ty.bitwidth()), ty)

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

    def Constant(c, ty):
        bw = ty.bitwidth()
        if ty.is_float():
            return Expr(FPVal(c, fps=get_fp_sort(bw)), ty)
        elif ty.is_int():
            return Expr(bv_const(c, bw), ty)
        else:
            raise NotImplementedError(f"Invalid type: {ty}")

    ##
    # variables
    def Var(name, ty):
        if ty.is_float():
            return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)
        else:
            assert ty.is_int(), ty
            return Expr(bv(name, ty.bitwidth()), ty)

    def BVVar(name, bw):
        return Expr(bv(name, bw), IntType(bw))

    def Bool(name):
        return Expr(Bool(name), BoolType())

    def Int1(name, ty):
        return BVSymbolicDomain.BVVar(name, 1)

    def Int8(name):
        return BVSymbolicDomain.BVVar(name, 8)

    def Int16(name):
        return BVSymbolicDomain.BVVar(name, 16)

    def Int32(name):
        return BVSymbolicDomain.BVVar(name, 32)

    def Int64(name):
        return BVSymbolicDomain.BVVar(name, 64)

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

    def Ite(c, a, b):
        assert BVSymbolicDomain.belongto(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return Expr(If(c.unwrap(), a.unwrap(), b.unwrap()), a.type())

    def And(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) & to_bv(b), IntType(a.bitwidth()))

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) | to_bv(b), IntType(a.bitwidth()))

    def Xor(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) ^ to_bv(b), IntType(a.bitwidth()))

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_bool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~to_bv(a), IntType(a.bitwidth()))

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        bw = b.value()
        assert a.bitwidth() <= bw, "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVZExt(bw - a.bitwidth(), ae), IntType(bw))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a), a
        assert b.is_concrete(), b
        assert b.is_int(), b
        bw = b.value()
        assert a.bitwidth() <= bw, "Invalid sext argument"

        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVSExt(bw - a.bitwidth(), ae), IntType(bw))

    def Cast(a: Value, ty: Type, signed: bool = True):
        """ Reinterpret cast """
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float():
            if a.is_int():
                if tybw > a.bitwidth():
                    # extend the bitvector
                    e = sext_expr(a, tybw) if signed else zext_expr(a, tybw)
                else:
                    e = a._expr
                if signed:
                    expr = fpToFP(RNE(), e, get_fp_sort(tybw))
                else:
                    expr = fpToFP(e, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        elif a.is_float() and ty.is_int():
            # if signed:
            #    ae = floatToSBV(a, ty)
            # else:
            #    ae = floatToUBV(a, ty)
            ae = fpToIEEEBV(a._expr)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)),
                        IntType(tybw))
        elif a.is_int() and ty.is_bool():
            return Expr(If(Ne(a.unwrap(), bv_const(0, a.bitwidth())),
                           TRUE(), FALSE()), BoolType())
        return None  # unsupported conversion

    def Extract(a, start, end):
        assert BVSymbolicDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        return Expr(
            BVExtract(end.value(), start.value(), a.unwrap()),
            IntType(end.value() - start.value() + 1),
        )

    def Concat(*args):
        l = len(args)
        assert l > 0, args
        assert BVSymbolicDomain.belongto(*args), args
        if l == 1:
            return args[0]
        return Expr(
            BVConcat(*(e.unwrap() for e in args)),
            IntType(sum(e.bitwidth() for e in args))
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

    def Le(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) <= to_bv(b), BoolType())

    def Lt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) < to_bv(b), BoolType())

    def Ge(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) >= to_bv(b), BoolType())

    def Gt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) > to_bv(b), BoolType())

    def Eq(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        return Expr(to_bv(a) == to_bv(b), BoolType())

    def Ne(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpNEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        return Expr(to_bv(a) != to_bv(b), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} + {b}"
        bw = a.bitwidth()
        if isfloat:
            # the operations on CPU work on doubles( well, 80-bits...)
            # and then truncate to float if needed
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae + be, bw), FloatType(bw))
        return Expr(to_bv(a) + to_bv(b), IntType(bw))

    def Sub(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} - {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae - be, bw), FloatType(bw))
        return Expr(to_bv(a) - to_bv(b), IntType(bw))

    def Mul(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} * {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae * be, bw), FloatType(bw))
        return Expr(to_bv(a) * to_bv(b), IntType(bw))

    def Div(a, b, unsigned=False, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} / {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae / be, bw), FloatType(bw))
        if unsigned:
            return Expr(UDiv(to_bv(a), to_bv(b)), IntType(bw))
        return Expr(to_bv(a) / to_bv(b), IntType(bw))

    def Rem(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)

    def Abs(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_float():
            return Expr(fpAbs(a.unwrap()), a.type())
        expr = a.unwrap()
        return Expr(If(expr < 0, -expr, expr), a.type())

    def Neg(a, isfloat):
        """ Return the negated number """
        assert BVSymbolicDomain.belongto(a)
        bw = a.bitwidth()
        if isfloat:
            return Expr(trunc_fp(fpNeg(to_double(a)), bw),
                        FloatType(bw))
        expr = a.unwrap()
        return Expr(-expr, a.type())

    def FpOp(op, val):
        assert BVSymbolicDomain.belongto(val)
        # FIXME: do not use the enum from instruction
        assert val.is_float()

        if op == FpOp.IS_INF:
            return Expr(fpIsInf(val.unwrap()), BoolType())
        if op == FpOp.IS_NAN:
            return Expr(fpIsNaN(val.unwrap()), BoolType())
        raise NotImplementedError("Invalid FP operation")


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
