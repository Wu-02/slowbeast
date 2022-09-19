from .domain import Domain
from typing import Union, Optional

from z3 import (
    BoolVal,
    FPVal,
    simplify,
    substitute,
    FP,
    Bool,
    And,
    Or,
    If,
    Xor,
    Not,
    ZeroExt as BVZExt,
    SignExt as BVSExt,
    fpToFP,
    fpFPToFP,
    RNE,
    fpToIEEEBV,
    fpSignedToFP,
    fpUnsignedToFP,
    Extract as BVExtract,
    Concat as BVConcat,
    LShR as BVLShR,
    fpLEQ,
    fpIsNaN,
    ULE as BVULE,
    fpLT,
    ULT as BVULT,
    fpGEQ,
    UGE as BVUGE,
    fpGT,
    UGT as BVUGT,
    fpEQ,
    fpNEQ,
    fpDiv,
    UDiv,
    URem,
    SRem,
    fpAbs,
    fpNeg,
    fpIsInf,
    fpIsZero,
    fpIsSubnormal,
    fpIsNegative,
)

from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.symbolic_helpers import (
    get_fp_sort,
    python_constant,
    python_to_sb_type,
    trunc_fp,
    to_double,
    to_bv,
    float_to_ubv,
    float_to_sbv,
    _bv_to_bool,
    TRUE,
    FALSE,
    bv,
    bv_const,
    bool_to_ubv,
    cast_to_fp,
)
from slowbeast.domains.expr import Expr
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import FpOp
from slowbeast.ir.types import BoolType, Type, BitVecType, FloatType
from slowbeast.util.debugging import FIXME


class BVSymbolicDomain(Domain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    @staticmethod
    def belongto(*args) -> bool:
        assert len(args) > 0
        for a in args:
            if a.KIND != 2:
                return False
        return True

    @staticmethod
    def lift(v: Value) -> Expr:
        assert isinstance(v, Value), f"Invalid value for lifting: {v}"
        if isinstance(v, Expr):
            return v

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), BoolType())
            ty = v.type()
            if v.is_float():
                return Expr(FPVal(v.value(), get_fp_sort(ty.bitwidth())), ty)
            return Expr(bv_const(v.value(), ty.bitwidth()), ty)

        raise NotImplementedError(f"Invalid value for lifting: {v}")

    @staticmethod
    def simplify(expr: Expr) -> Expr:
        return Expr(
            simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.type()
        )

    @staticmethod
    def to_python_constant(expr: Expr):
        return python_constant(expr.unwrap())

    @staticmethod
    def substitute(expr: Expr, *what) -> Union[ConcreteVal, Expr]:
        e = simplify(
            substitute(expr.unwrap(), *((a.unwrap(), b.unwrap()) for (a, b) in what))
        )
        c = python_constant(e)
        if c is not None:
            return ConcreteVal(c, python_to_sb_type(c, expr.type().bitwidth()))
        return Expr(e, expr.type())

    @staticmethod
    def Constant(c, ty: Type) -> Expr:
        bw = ty.bitwidth()
        if ty.is_float():
            return Expr(FPVal(c, fps=get_fp_sort(bw)), ty)
        elif ty.is_int():
            return Expr(bv_const(c, bw), ty)
        else:
            raise NotImplementedError(f"Invalid type: {ty}")

    ##
    # variables
    @staticmethod
    def Var(name: str, ty: Type) -> Expr:
        if ty.is_float():
            return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)
        elif ty.is_bool():
            return Expr(Bool(name), ty)
        else:
            assert ty.is_int() or ty.is_pointer(), ty
            return Expr(bv(name, ty.bitwidth()), ty)

    @staticmethod
    def BVVar(name, bw: int) -> Expr:
        return Expr(bv(name, bw), BitVecType(bw))

    @staticmethod
    def Bool(name: str) -> Expr:
        return Expr(Bool(name), BoolType())

    @staticmethod
    def Int1(name: str) -> Expr:
        return BVSymbolicDomain.BVVar(name, 1)

    @staticmethod
    def Int8(name: str) -> Expr:
        return BVSymbolicDomain.BVVar(name, 8)

    @staticmethod
    def Int16(name: str) -> Expr:
        return BVSymbolicDomain.BVVar(name, 16)

    @staticmethod
    def Int32(name: str) -> Expr:
        return BVSymbolicDomain.BVVar(name, 32)

    @staticmethod
    def Int64(name: str) -> Expr:
        return BVSymbolicDomain.BVVar(name, 64)

    ##
    # Logic operators
    @staticmethod
    def conjunction(*args) -> Expr:
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(And(*map(lambda x: _bv_to_bool(x.unwrap()), args)), BoolType())

    @staticmethod
    def disjunction(*args) -> Expr:
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(Or(*map(lambda x: _bv_to_bool(x.unwrap()), args)), BoolType())

    @staticmethod
    def Ite(c, a, b) -> Expr:
        assert BVSymbolicDomain.belongto(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return Expr(If(_bv_to_bool(c.unwrap()), a.unwrap(), b.unwrap()), a.type())

    @staticmethod
    def And(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) & to_bv(b), BitVecType(a.bitwidth()))

    @staticmethod
    def Or(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) | to_bv(b), BitVecType(a.bitwidth()))

    @staticmethod
    def Xor(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) ^ to_bv(b), BitVecType(a.bitwidth()))

    @staticmethod
    def Not(a) -> Expr:
        assert BVSymbolicDomain.belongto(a)
        if a.is_bool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~to_bv(a), BitVecType(a.bitwidth()))

    @staticmethod
    def ZExt(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        bw = b.value()
        assert a.bitwidth() <= bw, "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        ae = to_bv(a) if a.is_float() else bool_to_ubv(a)
        return Expr(BVZExt(bw - a.bitwidth(), ae), BitVecType(bw))

    @staticmethod
    def SExt(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a), a
        assert b.is_concrete(), b
        assert b.is_int(), b
        bw = b.value()
        assert a.bitwidth() <= bw, f"Invalid sext argument: {a} to {bw} bits"

        ae = to_bv(a) if a.is_float() else bool_to_ubv(a)
        return Expr(BVSExt(bw - a.bitwidth(), ae), BitVecType(bw))

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Expr]:
        """Static cast"""
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float() and a.is_bytes():
            # from IEEE bitvector
            expr = fpToFP(a.unwrap(), get_fp_sort(tybw))
            return Expr(expr, ty)
        if ty.is_float():
            if a.is_int():
                # from IEEE bitvector
                expr = fpToFP(a.unwrap(), get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        elif a.is_float() and ty.is_int():
            ae = fpToIEEEBV(a.unwrap())
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), BitVecType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float():
            if a.is_int():
                abw = a.bitwidth()
                if signed:  # from signed bitvector
                    expr = fpSignedToFP(RNE(), a.unwrap(), get_fp_sort(tybw))
                else:
                    expr = fpUnsignedToFP(RNE(), a.unwrap(), get_fp_sort(tybw))
                    # from IEEE bitvector
                    # expr = fpToFP(a._value, get_fp_sort(tybw))
                # expr = fpToFP(a._value, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
            if a.is_bytes():
                # from IEEE bitvector
                expr = fpToFP(a.unwrap(), get_fp_sort(a.bitwidth()))
                expr = fpFPToFP(RNE(), expr, get_fp_sort(tybw))
                return Expr(expr, ty)
        elif a.is_float() and ty.is_int():
            if signed:
                ae = float_to_sbv(a, ty)
            else:
                ae = float_to_ubv(a, ty)
            # ae = fpToIEEEBV(a._value)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), BitVecType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    @staticmethod
    def Extract(a, start, end) -> Expr:
        assert BVSymbolicDomain.belongto(a), a
        assert start.is_concrete(), start
        assert end.is_concrete(), end
        return Expr(
            BVExtract(end.value(), start.value(), a.unwrap()),
            BitVecType(end.value() - start.value() + 1),
        )

    @staticmethod
    def Concat(*args):
        l = len(args)
        assert l > 0, args
        assert BVSymbolicDomain.belongto(*args), args
        if l == 1:
            return args[0]
        return Expr(
            BVConcat(*(e.unwrap() for e in args)),
            BitVecType(sum(e.bitwidth() for e in args)),
        )

    @staticmethod
    def Shl(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) << b.unwrap(), BitVecType(a.bitwidth()))

    @staticmethod
    def AShr(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) >> b.unwrap(), BitVecType(a.bitwidth()))

    @staticmethod
    def LShr(a, b) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(BVLShR(to_bv(a), b.unwrap()), BitVecType(a.bitwidth()))

    @staticmethod
    def get_true() -> Expr:
        return Expr(TRUE(), BoolType())

    @staticmethod
    def get_false() -> Expr:
        return Expr(FALSE(), BoolType())

    ### Relational operators
    @staticmethod
    def Le(a: Expr, b: Expr, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpLEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) <= to_bv(b), BoolType())

    @staticmethod
    def Lt(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpLT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) < to_bv(b), BoolType())

    @staticmethod
    def Ge(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpGEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) >= to_bv(b), BoolType())

    @staticmethod
    def Gt(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpGT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) > to_bv(b), BoolType())

    @staticmethod
    def Eq(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} != {b}"
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if a.is_bool() and b.is_bool():
            return Expr(a == b, BoolType())
        return Expr(to_bv(a) == to_bv(b), BoolType())

    @staticmethod
    def Ne(a, b, unsigned: bool = False, floats: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = cast_to_fp(a), cast_to_fp(b)
            expr = fpNEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if a.is_bool() and b.is_bool():
            return Expr(a != b, BoolType())
        return Expr(to_bv(a) != to_bv(b), BoolType())

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a, b, isfloat: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} + {b}"
        bw = a.bitwidth()
        if isfloat:
            # the operations on CPU work on doubles( well, 80-bits...)
            # and then truncate to float if needed
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae + be, bw), FloatType(bw))
        return Expr(to_bv(a) + to_bv(b), BitVecType(bw))

    @staticmethod
    def Sub(a, b, isfloat: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} - {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae - be, bw), FloatType(bw))
        return Expr(to_bv(a) - to_bv(b), BitVecType(bw))

    @staticmethod
    def Mul(a, b, isfloat: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} * {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae * be, bw), FloatType(bw))
        return Expr(to_bv(a) * to_bv(b), BitVecType(bw))

    @staticmethod
    def Div(a, b, unsigned: bool = False, isfloat: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} / {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(fpDiv(RNE(), ae, be), bw), FloatType(bw))
        if unsigned:
            return Expr(UDiv(to_bv(a), to_bv(b)), BitVecType(bw))
        return Expr(to_bv(a) / to_bv(b), BitVecType(bw))

    @staticmethod
    def Rem(a, b, unsigned: bool = False) -> Expr:
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)

    @staticmethod
    def Abs(a) -> Expr:
        assert BVSymbolicDomain.belongto(a)
        if a.is_float():
            return Expr(fpAbs(a.unwrap()), a.type())
        expr = a.unwrap()
        return Expr(If(expr < 0, -expr, expr), a.type())

    @staticmethod
    def Neg(a, isfloat) -> Expr:
        """Return the negated number"""
        assert BVSymbolicDomain.belongto(a)
        bw = a.bitwidth()
        if isfloat:
            return Expr(trunc_fp(fpNeg(to_double(a)), bw), FloatType(bw))
        expr = a.unwrap()
        return Expr(-expr, a.type())

    @staticmethod
    def FpOp(op, val) -> Optional[Expr]:
        assert BVSymbolicDomain.belongto(val)
        # FIXME: do not use the enum from instruction
        assert val.is_float()

        if op == FpOp.IS_INF:
            return Expr(fpIsInf(val.unwrap()), BoolType())
        if op == FpOp.IS_NAN:
            return Expr(fpIsNaN(val.unwrap()), BoolType())
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.unwrap()
            expr = If(
                fpIsNaN(v),
                bv_const(0, 32),
                If(
                    fpIsInf(v),
                    bv_const(1, 32),
                    If(
                        fpIsZero(v),
                        bv_const(2, 32),
                        If(fpIsSubnormal(v), bv_const(3, 32), bv_const(4, 32)),
                    ),
                ),
            )
            return Expr(expr, BitVecType(32))
            if op == FpOp.SIGNBIT:
                return Expr(
                    If(fpIsNegative(bv_const(1, 32), bv_const(0, 32))), BitVecType(32)
                )

        return None