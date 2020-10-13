from slowbeast.ir.instruction import Assume, Assert, Cmp, Print
from slowbeast.ir.value import ConstantFalse, ConstantTrue, Constant
from slowbeast.ir.types import Type
from . utils import getLLVMOperands, getTypeSizeInBits

# FIXME: turn to a dict with separate handlers
special_functions = [
    '__assert_fail',
    '__VERIFIER_error',
    '__VERIFIER_assert',
    '__VERIFIER_assume',
    '__VERIFIER_assert',
    '__VERIFIER_silent_exit',
    '__INSTR_check_nontermination_header',
    '__INSTR_check_nontermination',
    '__INSTR_check_assume',
    '__INSTR_fail',
    '__slowbeast_print'
]


def create_special_fun(parser, inst, fun):
    """
    Return a pair R, S where R is the representant
    used for mapping of instructions and S is the sequence
    of instructions created
    """
    if fun == '__assert_fail':
        A = Assert(ConstantFalse, "assertion failed!")
        return A, [A]
    elif fun == '__VERIFIER_error':
        A = Assert(ConstantFalse, "__VERIFIER_error called!")
        return A, [A]
    elif fun == '__VERIFIER_assume':
        operands = getLLVMOperands(inst)
        cond = parser.getOperand(operands[0])
        C = Cmp(
            Cmp.NE, cond, Constant(
                0, Type(
                    getTypeSizeInBits(
                        operands[0].type))))
        A = Assume(C)
        return A, [C, A]
    elif fun == '__VERIFIER_silent_exit':
        A = Assume(ConstantFalse)
        return A, [A]
    elif fun == '__VERIFIER_assert' or fun == '__INSTR_check_assume':
        operands = getLLVMOperands(inst)
        cond = parser.getOperand(operands[0])
        C = Cmp(
            Cmp.NE, cond, Constant(
                0, Type(
                    getTypeSizeInBits(
                        operands[0].type))))
        A = Assert(C)
        return A, [C, A]
    elif fun == '__INSTR_check_nontermination_header':
        return None, []
    elif fun == '__INSTR_fail':
        A = Assert(ConstantFalse)
        return A, [A]
    elif fun == '__INSTR_check_nontermination':
        operands = getLLVMOperands(inst)
        cond = parser.getOperand(operands[0])
        C = Cmp(Cmp.NE, cond, ConstantTrue)
        A = Assert(C)
        return A, [C, A]
    elif fun == '__slowbeast_print':
        P = Print(*[parser.getOperand(x)
                    for x in getLLVMOperands(inst)[:-1]])
        return P, [P]
    else:
        raise NotImplementedError(
            "Unknown special function: {0}".format(fun))
