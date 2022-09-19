from typing import Union, List

from z3 import (
    is_const,
    is_app_of,
    SignExt as BVSExt,
    is_and,
    is_or,
    is_not,
    is_bv_value,
    simplify,
    If,
    Tactic,
    Z3_OP_SLEQ,
    Z3_OP_ULEQ,
    And,
    Then,
    With,
    BitVec,
    ZeroExt as BVZExt,
    is_bv,
    Or,
    Goal,
    Repeat,
    OrElse,
    is_fp,
    is_bool,
    Float32,
    Float64,
    Float128,
    is_true,
    is_false,
    is_fp_value,
    is_fprm_value,
    fpFPToFP,
    RNE,
    fpToFP,
    fpToIEEEBV,
    fpToUBV,
    BitVecSort,
    BoolVal,
    BitVecVal,
    Z3_OP_ITE,
    Z3_OP_SLT,
    Z3_OP_ULT,
    Z3_OP_SGEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGT,
    Z3_OP_UGT,
)

from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.ir.types import BoolType, FloatType, BitVecType


def subexpressions(expr):
    children = expr.children()
    for c in children:
        yield from subexpressions(c)
    yield expr


def _symbols(expr, ret: set) -> None:
    if _is_symbol(expr):
        ret.add(expr)
    else:
        for c in expr.children():
            _symbols(c, ret)


def symbols(expr):
    ret = set()
    _symbols(expr, ret)
    return ret


def to_cnf(*exprs):
    g = Goal()
    g.add(*exprs)
    t = Tactic("tseitin-cnf")
    goal = t(g)
    assert len(goal) == 1
    return goal[0]


def to_nnf(*exprs):
    g = Goal()
    g.add(*exprs)
    t = Tactic("nnf")
    goal = t(g)
    assert len(goal) == 1
    return goal[0]


def rewrite_simplify(*exprs):
    g = Goal()
    g.add(*exprs)
    t = Then(
        With("simplify", arith_lhs=True, som=True),
        Tactic("propagate-ineqs"),
        Tactic("normalize-bounds"),
        Tactic("propagate-values"),
        Tactic("simplify"),
    )
    return t(g)


def split_clauses(*exprs):
    g = Goal()
    g.add(*exprs)
    t = Repeat(OrElse(Tactic("split-clause"), Tactic("skip")))
    return t(g)


def solver_to_sb_type(s) -> Union[BoolType, FloatType, BitVecType]:
    if is_bv(s):
        return BitVecType(s.sort().size())
    if is_fp(s):
        srt = s.sort()
        return FloatType(srt.ebits() + srt.sbits())
    assert is_bool(s), f"Unhandled expression: {s}"
    return BoolType()


def get_fp_sort(bw):
    if bw == 32:
        return Float32()
    if bw == 64:
        return Float64()
    elif bw == 128:
        return Float128()
    raise NotImplementedError("Invalid FP type")


def zext_expr(a, bw):
    return BVZExt(bw - a.bitwidth(), bool_to_ubv(a))


def sext_expr(a, bw):
    return BVSExt(bw - a.bitwidth(), bool_to_ubv(a))


def python_constant(val):
    """
    Take a symbolic constant and get a python constant for it.
    Return None if the given expression is not a constant number
    or boolean
    """
    if is_bv_value(val):
        return val.as_long()
    elif is_true(val):
        return True
    elif is_false(val):
        return False
    return None


def python_to_sb_type(val: float, bw) -> Union[BoolType, FloatType, BitVecType]:
    if isinstance(val, bool):
        assert bw == 1
        return BoolType()
    if isinstance(val, int):
        return BitVecType(bw)
    if isinstance(val, float):
        return FloatType(bw)
    return None


def _is_symbol(expr):
    return (
        is_const(expr)
        and not is_bv_value(expr)
        and not is_fp_value(expr)
        and not is_fprm_value(expr)
    )


def trunc_fp(fexpr, bw):
    return simplify(fpFPToFP(RNE(), fexpr, get_fp_sort(bw)))


def to_double(x):
    bw = x.bitwidth()
    if x.is_float() and bw == 64:
        return x._value
    # we first must convert to float and then extend to double
    if x.is_float() and bw == 32:
        r = x._value
    else:
        assert not x.is_float()
        # bitcast from IEEE
        r = simplify(fpToFP(x._value, get_fp_sort(bw)))
    r = simplify(fpFPToFP(RNE(), r, Float64()))
    return r


def to_bv(x):
    if x.is_float():
        r = simplify(fpToIEEEBV(x._value))
        assert r.sort().size() == x.bitwidth(), f"{r.sort()}, {x.type()}"
        return r
    if x.is_bool():
        return bool_to_ubv(x)
    return x.unwrap()


def float_to_ubv(x, ty=None):
    if x.is_float():
        bw = ty.bitwidth() if ty else x.bitwidth()
        return simplify(fpToUBV(RNE(), x._value, BitVecSort(bw)))

    return x.unwrap()


def float_to_sbv(x, ty=None):
    if x.is_float():
        bw = ty.bitwidth() if ty else x.bitwidth()
        return simplify(fpToUBV(RNE(), x._value, BitVecSort(bw)))

    return x.unwrap()


def _bv_to_bool(b):
    if is_bool(b):
        return b
    return If(b != bv_const(0, b.sort().size()), TRUE(), FALSE())


def mk_or(*e):
    if len(e) == 1:
        return e[0]
    return Or(*map(_bv_to_bool, e))


def mk_and(*e):
    if len(e) == 1:
        return e[0]
    return And(*map(_bv_to_bool, e))


def mk_add(*e):
    if len(e) < 2:
        return e[0]
    expr = e[0] + e[1]
    for i in range(2, len(e)):
        expr = expr + e[i]
    return expr


def mk_mul(*e):
    if len(e) < 2:
        return e[0]
    expr = e[0] * e[1]
    for i in range(2, len(e)):
        expr = expr * e[i]
    return expr


def TRUE():
    return BoolVal(True)


def FALSE():
    return BoolVal(False)


def bv(name, bw):
    return BitVec(name, bw)


def bv_const(v, bw):
    return BitVecVal(v, bw)


def bool_to_bv(b):
    if not is_bool(b):
        return b
    return If(b, bv_const(1, 1), bv_const(0, 1))


def bool_to_ubv(b):
    if not b.is_bool():
        return b.unwrap()
    return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))


def cast_to_fp(b):
    if b.is_float():
        return b.unwrap()
    return fpToFP(b.unwrap(), get_fp_sort(b.type().bitwidth()))


def cast_to_bool(b):
    if b.is_bool():
        return b.unwrap()
    return If(b.unwrap() != bv_const(0, b.bitwidth()), TRUE(), FALSE())


def bv_size(bw):
    return bw.sort().size()


def to_c_expression(expr):
    "An auxiliary method for debugging that converts expr to C expression"

    if is_and(expr):
        return f"({' && '.join(map(to_c_expression, expr.children()))})"
    if is_or(expr):
        return f"({' || '.join(map(to_c_expression, expr.children()))})"
    if is_not(expr):
        return f"!({to_c_expression(expr.children()[0])})"

    chlds = expr.children()
    if is_app_of(expr, Z3_OP_ITE):
        return f"({to_c_expression(chlds[0])} ? {to_c_expression(chlds[1])} : {to_c_expression(chlds[2])} )"
    if is_app_of(expr, Z3_OP_SLEQ) or is_app_of(expr, Z3_OP_ULEQ):
        return f"({to_c_expression(chlds[0])}) <= ({to_c_expression(chlds[1])})"
    if is_app_of(expr, Z3_OP_SLT) or is_app_of(expr, Z3_OP_ULT):
        return f"({to_c_expression(chlds[0])}) < ({to_c_expression(chlds[1])})"
    if is_app_of(expr, Z3_OP_SGEQ) or is_app_of(expr, Z3_OP_UGEQ):
        return f"({to_c_expression(chlds[0])}) >= ({to_c_expression(chlds[1])})"
    if is_app_of(expr, Z3_OP_SGT) or is_app_of(expr, Z3_OP_UGT):
        return f"({to_c_expression(chlds[0])}) > ({to_c_expression(chlds[1])})"

    return str(expr)


def map_model(m, e) -> Union[None, List[None], List[ConcreteVal]]:
    if m is None:  # unsat
        return None
    ret = []
    for n, v in enumerate(e):
        if m[n] is None:
            ret.append(None)
        else:
            if v.is_float():
                val = m[n]
                if isinstance(val, BitVecNumRef):
                    f = val.as_long()
                elif isinstance(val, FPNumRef):
                    if val.isNaN():
                        f = float("NaN")
                    elif val.isInf():
                        if val.isNegative():
                            f = float("-inf")
                        else:
                            f = float("inf")
                    else:
                        f = float(eval(str(val)))
                else:
                    raise RuntimeError(f"Invalid model type: {v}")
                ret.append(ConcreteVal(f, v.type()))
            else:
                ret.append(ConcreteVal(m[n].as_long(), v.type()))
    return ret
