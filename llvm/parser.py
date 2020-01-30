from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.bblock import BBlock

from slowbeast.ir.value import *
from slowbeast.ir.types import *
from slowbeast.ir.instruction import *

import llvmlite.binding as llvm

def _get_llvm_module(path):
    if path.endswith('.ll'):
        with open(path, 'rt') as f:
            return llvm.parse_assembly(f.read())
    else:
        with open(path, 'rb') as f:
            return llvm.parse_bitcode(f.read())

def _getInt(s):
    try:
        return int(s)
    except ValueError:
        return None

def _getBitWidth(ty):
    if len(ty) < 2:
        return None
    if ty[0] != 'i':
        return None

    return _getInt(ty[1:])

def getConstantInt(val):
    # good, this is so ugly. But llvmlite does
    # not provide any other way...
    if val.type.is_pointer:
        return None

    assert '*' not in str(val)
    parts = str(val).split()
    if len(parts) != 2:
        return None

    bw = _getBitWidth(parts[0])
    if not bw:
        return None

    c = _getInt(parts[1])
    if c is None:
        return None

    return Constant(c, Type(bw))

def getLLVMOperands(inst):
    return [x for x in inst.operands]



class Parser:
    def __init__(self):
        self.program = Program()
        self._mapping = {}

    def getOperand(self, op):
        ret = getConstantInt(op)
        if not ret:
            ret = self._mapping.get(op)

        assert ret, "Do not have an operand: {0}".format(op)
        return ret

    def _createAlloca(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Array allocations not supported yet"

        A = Alloc(getConstantInt(operands[0]))
        A.addMetadata('llvm', str(inst))
        self._mapping[inst] = A

        return [A]

    def _createStore(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for store"

        S = Store(self.getOperand(operands[0]), self.getOperand(operands[1]))
        S.addMetadata('llvm', str(inst))
        return [S]


    def _createLoad(self, inst):
        return []
    def _createRet(self, inst):
        return []
    def _createArith(self, inst, opcode):
        return []

    def _parse_instruction(self, inst):
        if inst.opcode == 'alloca':
            return self._createAlloca(inst)
        elif inst.opcode == 'store':
            return self._createStore(inst)
        elif inst.opcode == 'load':
            return self._createLoad(inst)
        elif inst.opcode == 'ret':
            return self._createRet(inst)
        elif inst.opcode == 'add' or\
             inst.opcode == 'sub':
            return self._createArith(inst, inst.opcode)
        else:
            raise NotImplementedError("Unsupported instruction: {0}".format(inst))

    def _parse_block(self, F, block):
        """
        F     - slowbeast.Function
        block - llvm.block
        """
        B = BBlock(F)

        for inst in block.instructions:
            # the result of parsing one llvm instruction
            # may be several slowbeast instructions
            for I in self._parse_instruction(inst):
                B.append(I)

        assert B.getFunction() is F

    def _parse_fun(self, f):
        F = Function(f.name)
        self.program.addFun(F)

        for b in f.blocks:
            self._parse_block(F, b)

    def _parse_module(self, m):
        #XXX globals!

        for f in m.functions:
            self._parse_fun(f)

    def parse(self, path):
        m = _get_llvm_module(path)
        self._parse_module(m)

        # FIXME: set entry

        return self.program

if __name__ == "__main__":
    from sys import argv
    parser = Parser()
    P = parser.parse(argv[1])
    P.dump()

