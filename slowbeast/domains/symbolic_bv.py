from typing import Optional

from z3 import (
    If,
    ZeroExt as BVZExt,
    SignExt as BVSExt,
    fpToFP,
    fpFPToFP,
    RNE,
    fpSignedToFP,
    fpUnsignedToFP,
    Extract as BVExtract,
    Concat as BVConcat,
    LShR as BVLShR,
    ULE as BVULE,
    ULT as BVULT,
    UGE as BVUGE,
    UGT as BVUGT,
    UDiv,
    URem,
    SRem,
)

from slowbeast.domains.expr import Expr
from slowbeast.domains.symbolic_helpers import (
    get_fp_sort,
    to_bv,
    TRUE,
    FALSE,
    bv,
    bv_const,
    bool_to_ubv,
)
from slowbeast.domains.symbolic_value import SymbolicBytes
from slowbeast.domains.symbolic_z3 import Z3SymbolicDomain
from slowbeast.domains.value import Value
from slowbeast.ir.types import type_mgr, Type


class BVSymbolicDomain(Z3SymbolicDomain):
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    ##
    # variables
    @staticmethod
    def get_value(name: str, ty: Type) -> Expr:
        assert ty.is_bv() or ty.is_pointer(), ty
        return Expr(bv(name, ty.bitwidth()), ty)

    def get_constant(self, c, bw):
        return bv_const(c, bw)

    @staticmethod
    def And(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        # bitwise and
        return Expr(to_bv(a) & to_bv(b), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def Or(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        # bitwise and
        return Expr(to_bv(a) | to_bv(b), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def Xor(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        # bitwise and
        return Expr(to_bv(a) ^ to_bv(b), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def Not(a: Expr) -> Expr:
        assert isinstance(a, Expr), a
        return Expr(~to_bv(a), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def Extend(a: Value, bw: int, unsigned: bool) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(bw, int), bw
        assert a.bitwidth() <= bw, "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        ae = to_bv(a) if a.is_float() else bool_to_ubv(a)
        if unsigned:
            return Expr(BVZExt(bw - a.bitwidth(), ae), type_mgr().bv_ty(bw))
        return Expr(BVSExt(bw - a.bitwidth(), ae), type_mgr().bv_ty(bw))

    @staticmethod
    def BitCast(a: Value, ty: Type) -> Optional[Expr]:
        """Static cast"""
        assert isinstance(a, Expr), a
        tybw = ty.bitwidth()
        if a.is_bv():
            if ty.is_bool():
                return Expr(
                    If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                    type_mgr().bool_ty(),
                )
            if ty.is_float():
                # from IEEE bitvector
                expr = fpToFP(a.unwrap(), get_fp_sort(tybw))
                return Expr(expr, ty)
            if ty.is_bytes():
                return SymbolicBytes(
                    [
                        BVSymbolicDomain.Extract(a, 8 * off, 8 * off + 7)
                        for off in range(0, a.bytewidth())
                    ]
                )
        return None  # unsupported conversion

    @staticmethod
    def Cast(a: Value, ty: Type, signed: bool = True) -> Optional[Expr]:
        """Reinterpret cast"""
        assert isinstance(a, Expr), a
        tybw = ty.bitwidth()
        if ty.is_float():
            if a.is_bv():
                abw = a.bitwidth()
                if signed:  # from signed bitvector
                    expr = fpSignedToFP(RNE(), a.unwrap(), get_fp_sort(tybw))
                else:
                    expr = fpUnsignedToFP(RNE(), a.unwrap(), get_fp_sort(tybw))
                    # from IEEE bitvector
                    # expr = fpToFP(a._value, get_fp_sort(tybw))
                # expr = fpToFP(a._value, get_fp_sort(tybw))
                return Expr(expr, ty)
            if a.is_bytes():
                # from IEEE bitvector
                expr = fpToFP(a.unwrap(), get_fp_sort(a.bitwidth()))
                expr = fpFPToFP(RNE(), expr, get_fp_sort(tybw))
                return Expr(expr, ty)
        elif a.is_bool() and ty.is_bv():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)),
                type_mgr().bv_ty(tybw),
            )
        elif a.is_bv() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                type_mgr().bool_ty(),
            )
        return None  # unsupported conversion

    @staticmethod
    def Extract(a: Expr, start: int, end: int) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(start, int)
        assert isinstance(end, int)
        return Expr(
            BVExtract(end, start, a.unwrap()),
            type_mgr().bv_ty(end - start + 1),
        )

    @staticmethod
    def Concat(*args):
        l = len(args)
        assert l > 0, args
        if l == 1:
            return args[0]
        return Expr(
            BVConcat(*(e.unwrap() for e in args)),
            type_mgr().bv_ty(sum(e.bitwidth() for e in args)),
        )

    @staticmethod
    def Shl(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return Expr(to_bv(a) << b.unwrap(), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def AShr(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return Expr(to_bv(a) >> b.unwrap(), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def LShr(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert b.is_bv(), b
        return Expr(BVLShR(to_bv(a), b.unwrap()), type_mgr().bv_ty(a.bitwidth()))

    @staticmethod
    def get_true() -> Expr:
        return Expr(TRUE(), type_mgr().bool_ty())

    @staticmethod
    def get_false() -> Expr:
        return Expr(FALSE(), type_mgr().bool_ty())

    ### Relational operators
    @staticmethod
    def Le(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        if unsigned:
            return Expr(BVULE(to_bv(a), to_bv(b)), type_mgr().bool_ty())
        return Expr(to_bv(a) <= to_bv(b), type_mgr().bool_ty())

    @staticmethod
    def Lt(a, b, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:
            return Expr(BVULT(to_bv(a), to_bv(b)), type_mgr().bool_ty())
        return Expr(to_bv(a) < to_bv(b), type_mgr().bool_ty())

    @staticmethod
    def Ge(a, b, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:
            return Expr(BVUGE(to_bv(a), to_bv(b)), type_mgr().bool_ty())
        return Expr(to_bv(a) >= to_bv(b), type_mgr().bool_ty())

    @staticmethod
    def Gt(a, b, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if unsigned:
            return Expr(BVUGT(to_bv(a), to_bv(b)), type_mgr().bool_ty())
        return Expr(to_bv(a) > to_bv(b), type_mgr().bool_ty())

    @staticmethod
    def Eq(a, b) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a} != {b}"
        return Expr(to_bv(a) == to_bv(b), type_mgr().bool_ty())

    @staticmethod
    def Ne(a, b) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        return Expr(to_bv(a) != to_bv(b), type_mgr().bool_ty())

    ##
    # Arithmetic operations
    @staticmethod
    def Add(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert (
            a.type() == b.type()
        ), f"Operation on invalid types: {a.type()} != {b.type()}"
        assert a.bitwidth() == b.bitwidth(), f"{a} + {b}"
        bw = a.bitwidth()
        return Expr(to_bv(a) + to_bv(b), type_mgr().bv_ty(bw))

    @staticmethod
    def Sub(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.bitwidth() == b.bitwidth(), f"{a} - {b}"
        bw = a.bitwidth()
        return Expr(to_bv(a) - to_bv(b), type_mgr().bv_ty(bw))

    @staticmethod
    def Mul(a: Expr, b: Expr) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.bitwidth() == b.bitwidth(), f"{a} * {b}"
        bw = a.bitwidth()
        return Expr(to_bv(a) * to_bv(b), type_mgr().bv_ty(bw))

    @staticmethod
    def Div(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.bitwidth() == b.bitwidth(), f"{a} / {b}"
        bw = a.bitwidth()
        if unsigned:
            return Expr(UDiv(to_bv(a), to_bv(b)), type_mgr().bv_ty(bw))
        return Expr(to_bv(a) / to_bv(b), type_mgr().bv_ty(bw))

    @staticmethod
    def Rem(a: Expr, b: Expr, unsigned: bool = False) -> Expr:
        assert isinstance(a, Expr), a
        assert isinstance(b, Expr), b
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)

    @staticmethod
    def Abs(a: Expr) -> Expr:
        assert isinstance(a, Expr), a
        expr = a.unwrap()
        return Expr(If(expr < 0, -expr, expr), a.type())

    @staticmethod
    def Neg(a: Expr) -> Expr:
        """Return the negated number"""
        assert isinstance(a, Expr), a
        bw = a.bitwidth()
        expr = a.unwrap()
        return Expr(-expr, a.type())
