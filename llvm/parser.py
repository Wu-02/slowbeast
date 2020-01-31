from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.bblock import BBlock

from slowbeast.ir.value import *
from slowbeast.ir.types import *
from slowbeast.ir.instruction import *

from slowbeast.util.debugging import print_stderr

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

def getTypeSizeInBits(ty):
    if not isinstance(ty, str) and ty.is_pointer:
        #FIXME: get it from target triple
        return 64

    sty = str(ty)
    if sty.startswith('['):
        print()
        parts = sty[1:-1].split()
        print(parts)
        if len(parts) != 3 or parts[1] != 'x':
            return None
        elemType = getTypeSizeInBits(parts[2])
        num = _getInt(parts[0])
        print(elemType)
        print(num)
        if elemType and num:
            return elemType * num
        return None
    else:
        assert '*' not in sty
        return _getBitWidth(sty)

def getTypeSize(ty):
    ts = getTypeSizeInBits(ty)
    if ts:
        return int(max(ts/8, 1))
    return None

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

def parseCmp(inst):
    parts = str(inst).split()
    if len(parts) != 7:
        return None, False
    if parts[2] != 'icmp':
        return None, False

    if parts[3] == 'eq':
        return Cmp.EQ, False
    elif parts[3] == 'ne':
        return Cmp.NE, False
    elif parts[3] == 'le' or parts[3] == 'sle':
        return Cmp.LE, False
    elif parts[3] == 'ge' or parts[3] == 'sge':
        return Cmp.GE, False
    elif parts[3] == 'lt' or parts[3] == 'slt':
        return Cmp.LT, False
    elif parts[3] == 'gt' or parts[3] == 'sgt':
        return Cmp.GT, False
    elif parts[3] == 'ule':
        return Cmp.LE, True
    elif parts[3] == 'uge':
        return Cmp.GE, True
    elif parts[3] == 'ult':
        return Cmp.LT, True
    elif parts[3] == 'ugt':
        return Cmp.GT, True

    else:
        return None, False

class Parser:
    def __init__(self):
        self.program = Program()
        self._bblocks = {}
        self._mapping = {}
        self._metadata_opts = ['llvm']

        # FIXME: get rid of this once we support
        # parsing the stuff inside __assert_fail
        self._special_funs = ['__assert_fail',
                              '__slowbeast_print']

    def getOperand(self, op):
        ret = self._mapping.get(op)
        if not ret:
            ret = getConstantInt(op)

        assert ret, "Do not have an operand: {0}".format(op)
        return ret

    def getBBlock(self, llvmb):
        return self._bblocks[llvmb]

    def getFun(self, fn):
        return self.program.getFunction(fn)

    def _addMapping(self, llinst, sbinst):
        if 'llvm' in self._metadata_opts:
            sbinst.addMetadata('llvm', str(llinst))
        self._mapping[llinst] = sbinst

    def _createAlloca(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Array allocations not supported yet"

        tySize = getTypeSize(inst.type.element_type)
        assert tySize and tySize > 0, "Invalid type size"
        num = getConstantInt(operands[0])
        assert num and num.getValue() > 0, "Invalid number of elements of allocation"

        # XXX: shouldn't we use SizeType instead?
        A = Alloc(Constant(tySize*num.getValue(), Type(num.getBitWidth())))
        self._addMapping(inst, A)
        return [A]

    def _createStore(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for store"

        S = Store(self.getOperand(operands[0]), self.getOperand(operands[1]))
        self._addMapping(inst, S)
        return [S]

    def _createLoad(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"

        bytesNum = getTypeSize(inst.type)
        assert bytesNum, "Could not get the size of type"
        L = Load(self.getOperand(operands[0]), bytesNum)
        self._addMapping(inst, L)
        return [L]

    def _createRet(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) <= 1, "Invalid number of operands for ret"

        if len(operands) == 0:
            R = Return()
        else:
            R = Return(self.getOperand(operands[0]))

        self._addMapping(inst, R)
        return [R]

    def _createArith(self, inst, opcode):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for store"

        op1 = self.getOperand(operands[0])
        op2 = self.getOperand(operands[1])
        if opcode == 'add':
            I = Add(op1, op2)
        elif opcode == 'sub':
            I = Sub(op1, op2)
        elif opcode == 'mul':
            I = Mul(op1, op2)
        elif opcode == 'div':
            I = Div(op1, op2)
        else:
            raise NotImplementedError("Artihmetic operation unsupported: {0}".format(inst))

        self._addMapping(inst, I)
        return [I]

    def _createCmp(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for cmp"
        P, is_unsigned = parseCmp(inst)
        if not P:
            raise NotImplementedError("Unsupported cmp instruction: {0}".format(inst))

        C = Cmp(P, self.getOperand(operands[0]),
                self.getOperand(operands[1]),
                is_unsigned)
        self._addMapping(inst, C)
        return [C]

    def _createBranch(self, inst):
        operands = getLLVMOperands(inst)
        if len(operands) == 3:
            cond = self.getOperand(operands[0])
            # XXX: whaat? for some reason, the bindings return
            # the false branch as first
            b1 = self.getBBlock(operands[2])
            b2 = self.getBBlock(operands[1])
            B = Branch(cond, b1, b2)
        elif len(operands) == 1:
            b1 = self.getBBlock(operands[0])
            B = Branch(ConstantTrue, b1, b1)
        else:
            raise NotImplementedError("Invalid number of operands for br")
        self._addMapping(inst, B)
        return [B]

    def _createSpecialCall(self, inst, fun):
        if fun == '__assert_fail':
            A = Assert(ConstantFalse, "assertion failed!")
            self._addMapping(inst, A)
            return [A]
        elif fun == '__slowbeast_print':
            P = Print(*[self.getOperand(x) for x in getLLVMOperands(inst)[:-1]])
            self._addMapping(inst, P)
            return [P]
        else:
            raise NotImplementedError("Unknown special function: {0}".format(fun))

    def _createCall(self, inst):
        #import pdb
        #pdb.set_trace()
        operands = getLLVMOperands(inst)
        fun = operands[-1].name
        if not fun:
            raise NotImplementedError("Unsupported call: {0}".format(inst))

        if fun in self._special_funs:
            return self._createSpecialCall(inst, fun)

        F = self.getFun(fun)
        if not F:
            raise NotImplementedError("Unknown function: {0}".format(fun))

        C = Call(F, *[self.getOperand(x) for x in getLLVMOperands(inst)[:-1]])
        self._addMapping(inst, C)
        return [C]

    def _createUnreachable(self, inst):
        A = Assert(ConstantFalse, "unreachable")
        self._addMapping(inst, A)
        return [A]

    def _createZExt(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        zext = ZExt(self.getOperand(operands[0]), Constant(getTypeSizeInBits(inst.type), Type(32)))
        self._addMapping(inst, zext)
        return [zext]

    def _parse_instruction(self, inst):
        if inst.opcode == 'alloca':
            return self._createAlloca(inst)
        elif inst.opcode == 'store':
            return self._createStore(inst)
        elif inst.opcode == 'load':
            return self._createLoad(inst)
        elif inst.opcode == 'ret':
            return self._createRet(inst)
        elif inst.opcode == 'icmp':
            return self._createCmp(inst)
        elif inst.opcode == 'br':
            return self._createBranch(inst)
        elif inst.opcode == 'call':
            return self._createCall(inst)
        elif inst.opcode == 'unreachable':
            return self._createUnreachable(inst)
        elif inst.opcode == 'zext':
            return self._createZExt(inst)
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
        B = self.getBBlock(block)
        assert B, "Do not have a bblock"

        for inst in block.instructions:
            # the result of parsing one llvm instruction
            # may be several slowbeast instructions
            try:
                instrs = self._parse_instruction(inst)
                assert inst.opcode in ['zext'] or instrs, "No instruction was created"
                for I in instrs:
                    B.append(I)
            except Exception as e:
                print_stderr("Failed parsing llvm while parsing: {0}".format(inst), color="RED")
                raise e

        assert B.getFunction() is F

    def _parse_fun(self, f):
        F = self.getFun(f.name)

        # add mapping to arguments of the function
        n = 0
        for a in f.arguments:
            self._addMapping(a, F.getArgument(n))
            n += 1

        # first create blocks as these can be operands to br instructions
        for b in f.blocks:
            self._bblocks[b] = BBlock(F)

        for b in f.blocks:
            self._parse_block(F, b)

    def _parse_module(self, m):
        #XXX globals!

        # create the function at first,
        # because they may be operands of calls
        for f in m.functions:
            self.program.addFun(Function(f.name, len(list(f.arguments))))

        for f in m.functions:
            self._parse_fun(f)

    def _parse(self, path):
        m = _get_llvm_module(path)
        self._parse_module(m)

        # FIXME: set entry here?

        return self.program

    def parse(self, path):
        try:
            return self._parse(path)
        except NotImplementedError as e:
            print_stderr(str(e), color="RED")
            return None
        except AssertionError as e:
            print_stderr(str(e), color="RED")
            return None

if __name__ == "__main__":
    from sys import argv
    parser = Parser()
    P = parser.parse(argv[1])
    P.dump()

