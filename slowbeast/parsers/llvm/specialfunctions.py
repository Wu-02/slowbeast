from slowbeast.ir.instruction import (
    Alloc,
    Assume,
    Assert,
    Cmp,
    Print,
    Abs,
    FpOp,
    Cast,
)
from slowbeast.ir.types import get_size_type_size, type_mgr
from slowbeast.util.debugging import print_stderr
from .utils import get_llvm_operands, type_size_in_bits, to_float_ty, get_sb_type
from ...domains.concrete import ConstantTrue, ConstantFalse, ConcreteDomain

concrete_value = ConcreteDomain.get_value

# FIXME: turn to a dict with separate handlers
special_functions = [
    "llvm.fabs.f32",
    "llvm.fabs.f64",
    "fesetround",
    "nan",
    "__isnan",
    "__isnanf",
    "__isnanl",
    "__isinf",
    "__isinff",
    "__isinfl",
    # NOTE: do we want to implement these as instructions? Probably not...
    "__fpclassify",
    "__fpclassifyf",
    "__fpclassifyl",
    "__signbit",
    "__signbitf",
    "__signbitl",
    "malloc",
    "__assert_fail",
    "__VERIFIER_error",
    "__VERIFIER_assume",
    "verifier.assume",
    "assume_abort_if_not",
    "__VERIFIER_silent_exit",
    "__INSTR_check_nontermination_header",
    "__INSTR_check_nontermination",
    "__INSTR_check_assume",
    "__INSTR_fail",
    "__slowbeast_print",
    "ldv_stop",
]


def create_special_fun(parser, inst, fun, error_funs, to_check):
    """
    Return a pair R, S where R is the representant
    used for mapping of instructions and S is the sequence
    of instructions created
    """
    module = parser.llvmmodule
    no_overflow = to_check and "no-signed-overflow" in to_check
    ignore_asserts = len(error_funs) > 0 or no_overflow
    if fun in error_funs:
        A = Assert(ConstantFalse, "error function called!")
        return A, [A]
    elif fun == "__assert_fail":
        if ignore_asserts:
            # ignore assertions if error functions are given
            A = Assume(ConstantFalse)
        else:
            A = Assert(ConstantFalse, "assertion failed!")
        return A, [A]
    elif fun == "__VERIFIER_error":
        if ignore_asserts:
            # ignore assertions if error functions are given
            A = Assume(ConstantFalse)
        else:
            A = Assert(ConstantFalse, "__VERIFIER_error called!")
        return A, [A]
    elif fun in ("__VERIFIER_assume", "assume_abort_if_not", "verifier.assume"):
        operands = get_llvm_operands(inst)
        cond = parser.operand(operands[0])
        optypes = [get_sb_type(module, op.type) for op in operands]
        C = Cmp(
            Cmp.NE,
            cond,
            concrete_value(0, type_size_in_bits(module, operands[0].type)),
            optypes,
        )
        A = Assume(C)
        return A, [C, A]
    elif fun in ("__VERIFIER_silent_exit", "ldv_stop"):
        print_stderr("Assuming that ldv_stop is assume(false)...", color="orange")
        A = Assume(ConstantFalse)
        return A, [A]
    elif no_overflow and fun.startswith("__ubsan_handle"):
        A = Assert(ConstantFalse, "signed integer overflow")
        return A, [A]
    elif fun == "__INSTR_check_assume":
        operands = get_llvm_operands(inst)
        cond = parser.operand(operands[0])
        optypes = [get_sb_type(module, op.type) for op in operands]
        C = Cmp(
            Cmp.NE,
            cond,
            concrete_value(0, type_size_in_bits(module, operands[0].type)),
            optypes,
        )
        A = Assert(C)
        return A, [C, A]
    elif fun == "__INSTR_check_nontermination_header":
        return None, []
    elif fun == "__INSTR_fail":
        A = Assert(ConstantFalse)
        return A, [A]
    elif fun == "__INSTR_check_nontermination":
        operands = get_llvm_operands(inst)
        cond = parser.operand(operands[0])
        C = Cmp(Cmp.NE, cond, ConstantTrue)
        A = Assert(C)
        return A, [C, A]
    elif fun == "malloc":
        operands = get_llvm_operands(inst)
        assert (
            len(operands) == 2
        ), "Invalid malloc"  # (call has +1 operand for the function)
        size = parser.operand(operands[0])
        A = Alloc(size, on_heap=True)
        return A, [A]
    elif fun.startswith("llvm.fabs."):
        operands = get_llvm_operands(inst)
        val = parser.operand(operands[0])
        A = Abs(
            val,
            type_mgr().float_ty(type_size_in_bits(module, inst.type)),
            [get_sb_type(module, operands[0].type)],
        )
        return A, [A]
    elif fun in ("__isinf", "__isinff", "__isinfl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.IS_INF, val)
        P = Extend(
            O,
            concrete_value(type_size_in_bits(module, inst.type), get_size_type_size()),
            True,  # unsigned
        )
        return P, [O, P]
    elif fun in "nan":
        I = Cast(concrete_value(float("NaN"), 64), type_mgr().float_ty(64))
        return I, [I]
    elif fun in ("__isnan", "__isnanf", "__isnanfl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.IS_NAN, val)
        # the functions return int
        P = Extend(
            O,
            concrete_value(type_size_in_bits(module, inst.type), get_size_type_size()),
            True,  # unsigned
        )
        return P, [O, P]
    elif fun in ("__fpclassify", "__fpclassifyf", "__fpclassifyl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.FPCLASSIFY, val)
        # the functions return int
        return O, [O]
    elif fun in ("__signbit", "__signbitf", "__signbitl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.SIGNBIT, val)
        # the functions return int
        return O, [O]
    elif fun == "fesetround":
        raise NotImplementedError("fesetround is not supported yet")
    elif fun == "__slowbeast_print":
        P = Print(*[parser.operand(x) for x in get_llvm_operands(inst)[:-1]])
        return P, [P]
    else:
        raise NotImplementedError(f"Unknown special function: {fun}")
