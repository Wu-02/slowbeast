from slowbeast.ir.instruction import (
    Alloc,
    Assume,
    Assert,
    Cmp,
    Print,
    Abs,
    FpOp,
    Cast,
    BinaryOperation,
    Extend,
)
from slowbeast.ir.types import type_mgr
from slowbeast.util.debugging import print_stderr
from .utils import get_llvm_operands, type_size_in_bits, to_float_ty, get_sb_type
from ...domains.concrete import ConstantFalse, ConcreteDomain
from ...domains.concrete_floats import ConcreteFloat

concrete_value = ConcreteDomain.get_value

# FIXME: turn to a dict with separate handlers
special_functions = [
    "llvm.fabs.f32",
    "llvm.fabs.f64",
    "llvm.fmuladd.f32",
    "llvm.fmuladd.f64",
    "llvm.minnum.f32",
    "llvm.minnum.f64",
    "llvm.round.f32",
    "llvm.round.f64",
    "llvm.floor.f32",
    "llvm.floor.f64",
    "llvm.ceil.f32",
    "llvm.ceil.f64",
    "llvm.trunc.f32",
    "llvm.trunc.f64",
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
    "calloc",
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
    elif fun == "malloc":
        operands = get_llvm_operands(inst)
        assert (
            len(operands) == 2
        ), "Invalid malloc"  # (call has +1 operand for the function)
        size = parser.operand(operands[0])
        A = Alloc(size, on_heap=True)
        return A, [A]
    elif fun == "calloc":
        operands = get_llvm_operands(inst)
        assert (
            len(operands) == 3
        ), "Invalid calloc"  # (call has +1 operand for the function)
        size = BinaryOperation(
            BinaryOperation.MUL,
            parser.operand(operands[0]),
            parser.operand(operands[1]),
            [get_sb_type(module, operands[i].type) for i in (0, 1)],
        )
        A = Alloc(size, on_heap=True, zeroed=True)
        return A, [size, A]
    elif fun.startswith("llvm.fabs."):
        operands = get_llvm_operands(inst)
        val = parser.operand(operands[0])
        A = Abs(
            val,
            type_mgr().float_ty(type_size_in_bits(module, inst.type)),
            [get_sb_type(module, operands[0].type)],
        )
        return A, [A]
    elif fun.startswith("llvm.fmuladd."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 3)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 3)]
        MUL = BinaryOperation(BinaryOperation.MUL, ops[0], ops[1], types[:2])
        ADD = BinaryOperation(BinaryOperation.ADD, MUL, ops[2], [MUL.type(), types[2]])
        return ADD, [MUL, ADD]
    elif fun.startswith("llvm.minnum."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 2)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 2)]
        MIN = FpOp(FpOp.MIN, ops, types)
        return MIN, [MIN]
    elif fun.startswith("llvm.round."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 1)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 1)]
        ROUND = FpOp(FpOp.ROUND, ops, types)
        return ROUND, [ROUND]
    elif fun.startswith("llvm.floor."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 1)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 1)]
        fpop = FpOp(FpOp.FLOOR, ops, types)
        return fpop, [fpop]
    elif fun.startswith("llvm.ceil."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 1)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 1)]
        fpop = FpOp(FpOp.CEIL, ops, types)
        return fpop, [fpop]
    elif fun.startswith("llvm.trunc."):
        operands = get_llvm_operands(inst)
        ops = [parser.operand(operands[i]) for i in range(0, 1)]
        types = [get_sb_type(module, operands[i].type) for i in range(0, 1)]
        fpop = FpOp(FpOp.TRUNC, ops, types)
        return fpop, [fpop]
    elif fun in ("__isinf", "__isinff", "__isinfl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.IS_INF, [val], [get_sb_type(module, inst.operands[0].type)])
        P = Extend(
            O,
            type_size_in_bits(module, inst.type),
            True,  # unsigned
            [get_sb_type(module, inst.operands[0].type)],
        )
        return P, [O, P]
    elif fun in "nan":
        I = Cast(
            ConcreteFloat("NaN", 64),
            type_mgr().float_ty(64),
            True,
            [get_sb_type(module, inst.operands[0].type)],
        )
        return I, [I]
    elif fun in ("__isnan", "__isnanf", "__isnanfl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.IS_NAN, [val], [get_sb_type(module, inst.operands[0].type)])
        # the functions return int
        P = Extend(
            O,
            type_size_in_bits(module, inst.type),
            True,  # unsigned
            [get_sb_type(module, inst.operands[0].type)],
        )
        return P, [O, P]
    elif fun in ("__fpclassify", "__fpclassifyf", "__fpclassifyl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.FPCLASSIFY, [val], [get_sb_type(module, inst.operands[0].type)])
        # the functions return int
        return O, [O]
    elif fun in ("__signbit", "__signbitf", "__signbitl"):
        val = to_float_ty(parser.operand(get_llvm_operands(inst)[0]))
        O = FpOp(FpOp.SIGNBIT, [val], [get_sb_type(module, inst.operands[0].type)])
        # the functions return int
        return O, [O]
    elif fun == "fesetround":
        raise NotImplementedError("fesetround is not supported yet")
    elif fun == "__slowbeast_print":
        P = Print(*[parser.operand(x) for x in get_llvm_operands(inst)[:-1]])
        return P, [P]
    else:
        raise NotImplementedError(f"Unknown special function: {fun}")
