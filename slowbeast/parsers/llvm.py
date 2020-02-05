from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.bblock import BBlock

from slowbeast.ir.value import *
from slowbeast.ir.types import *
from slowbeast.ir.instruction import *

from slowbeast.util.debugging import print_stderr, warn

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
        if s.startswith('0x'):
            return int(s, 16)
        else:
            if 'e' in s: # scientific notation
                if float(s) > 0 or float(s) < 0:
                    warn("Concretized float number: {0}".format(s))
                    #return None
                return int(float(s))
            else:
                return int(s)
    except ValueError:
        return None

def _getBitWidth(ty):
    if len(ty) < 2:
        return None
    if ty[0] == 'i':
        return _getInt(ty[1:])
    elif ty.startswith('double'):
        # FIXME: get this from program
        return 64
    elif ty.startswith('float'):
        return 32
    else:
        return None

def isPointerTy(ty):
    if isinstance(ty, str):
        return ty[-1] == '*'

    assert ty.is_pointer == isPointerTy(str(ty))
    return ty.is_pointer

def isArrayTy(ty):
    sty=str(ty)
    if len(sty) < 2:
        return False
    return sty[0] == '[' and sty[-1] == ']'

def parseArrayTy(ty):
    assert isArrayTy(ty)
    sty = str(ty)
    parts = sty[1:-1].split()
    assert len(parts) == 3 and parts[1] == 'x', "Unhandled array type"

    return parts[0], parts[2]

def getTypeSizeInBits(ty):
    if not isinstance(ty, str) and ty.is_pointer:
        #FIXME: get it from target triple
        return 64

    sty = str(ty)
    if isArrayTy(ty):
        num, elemType = parseArrayTy(ty)
        elemType = getTypeSizeInBits(elemType)
        num = _getInt(num)
        if elemType and num:
            return elemType * num
        return None
    # FIXME: get it from target triple
    elif sty == 'double':
        return 64
    elif sty == 'float':
        return 32
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

    if '*' in str(val):
        return None
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
    if parts[1] != '=' and parts[2] != 'icmp':
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

def parseFunctionRetTy(ty):
    parts = str(ty).split()
    if len(parts) < 2:
        return False, None
    if parts[0] == 'void':
        return True, None
    else:
        sz = getTypeSizeInBits(parts[0])
        if sz:
            return True, Type(sz)
    return False, None

class Parser:
    def __init__(self):
        self.program = Program()
        self._bblocks = {}
        self._mapping = {}
        self._metadata_opts = ['llvm']
        # records about PHIs that we created. We must place
        # the writes emulating PHIs only after all blocks were created.
        self.phis = []

        # FIXME: get rid of this once we support
        # parsing the stuff inside __assert_fail
        self._special_funs = ['__assert_fail', '__VERIFIER_error',
                              '__VERIFIER_assume',
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
        assert self._mapping.get(llinst) is None, "Duplicated mapping"
        self._mapping[llinst] = sbinst

    def _createAlloca(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Array allocations not supported yet"

        tySize = getTypeSize(inst.type.element_type)
        assert tySize and tySize > 0, "Invalid type size"
        num = self.getOperand(operands[0])

        if isinstance(num, ValueInstruction): #VLA
            M = Mul(Constant(tySize, SizeType), num)
            A = Alloc(M)
            self._addMapping(inst, A)
            return [M, A]
        else:
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
        elif opcode == 'udiv':
            I = Div(op1, op2, unsigned=True)
        else:
            raise NotImplementedError("Artihmetic operation unsupported: {0}".format(inst))

        self._addMapping(inst, I)
        return [I]

    def _createShift(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for shift"

        op1 = self.getOperand(operands[0])
        op2 = self.getOperand(operands[1])
        opcode = inst.opcode

        if opcode == 'shl':
            I = Shl(op1, op2)
        elif opcode == 'lshr':
            I = LShr(op1, op2)
        elif opcode == 'ashr':
            I = AShr(op1, op2)
        else:
            raise NotImplementedError("Shift operation unsupported: {0}".format(inst))

        self._addMapping(inst, I)
        return [I]

    def _createLogicOp(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for logic op"

        op1 = self.getOperand(operands[0])
        op2 = self.getOperand(operands[1])
        opcode = inst.opcode

        if opcode == 'and':
            I = And(op1, op2)
        elif opcode == 'or':
            I = Or(op1, op2)
        elif opcode == 'xor':
            I = Xor(op1, op2)
        else:
            raise NotImplementedError("Logic operation unsupported: {0}".format(inst))

        self._addMapping(inst, I)
        return [I]

    def _createRem(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for rem"

        op1 = self.getOperand(operands[0])
        op2 = self.getOperand(operands[1])
        opcode = inst.opcode

        if opcode == 'srem':
            I = Rem(op1, op2)
        elif opcode == 'urem':
            I = Rem(op1, op2, unsigned=True)
        else:
            raise NotImplementedError("Remainder operation unsupported: {0}".format(inst))

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
        elif fun == '__VERIFIER_error':
            A = Assert(ConstantFalse, "__VERIFIER_error called!")
            self._addMapping(inst, A)
            return [A]
        elif fun == '__VERIFIER_assume':
            operands=getLLVMOperands(inst)
            cond = self.getOperand(operands[0])
            C = Cmp(Cmp.NE, cond, Constant(0, Type(getTypeSizeInBits(operands[0].type))))
            A = Assume(C)
            self._addMapping(inst, A)
            return [C, A]
        elif fun == '__slowbeast_print':
            P = Print(*[self.getOperand(x) for x in getLLVMOperands(inst)[:-1]])
            self._addMapping(inst, P)
            return [P]
        else:
            raise NotImplementedError("Unknown special function: {0}".format(fun))

    def _createCall(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) > 0

        # uffff, llvmlite really sucks in parsing LLVM.
        # We cannot even get constantexprs...
        fun = operands[-1].name
        if not fun:
            sop = str(operands[-1])
            if 'bitcast' in sop:
                for x in sop.split():
                    if x[0] == '@':
                        fun = x[1:]
                        if self.getFun(fun):
                            break
                        else:
                            fun = None
        if not fun:
            raise NotImplementedError("Unsupported call: {0}".format(inst))

        if fun.startswith('llvm.dbg'):
            return []

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
        zext = ZExt(self.getOperand(operands[0]), Constant(getTypeSizeInBits(inst.type), Type(32)))
        self._addMapping(inst, zext)
        return [zext]

    def _createSExt(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        sext = SExt(self.getOperand(operands[0]), Constant(getTypeSizeInBits(inst.type), Type(32)))
        self._addMapping(inst, sext)
        return [sext]

    def _createTrunc(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        bits=getTypeSizeInBits(inst.type)
        ext = ExtractBits(self.getOperand(operands[0]), Constant(0, Type(32)), Constant(bits-1, Type(32)))
        self._addMapping(inst, ext)
        return [ext]

    def _createCast(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        bits=getTypeSizeInBits(inst.type)
        op = self.getOperand(operands[0])
        if op.isConstant():
            self._mapping[inst] = op
            return []
        else:
            raise NotImplementedError("Unhandled cast: {0}".format(inst))

    def _createGep(self, inst):
        operands = getLLVMOperands(inst)
        assert isPointerTy(operands[0].type), "First type of GEP is not a pointer"
        ty = operands[0].type.element_type
        elemSize = getTypeSize(ty)
        shift = 0
        varIdx = []
        for idx in operands[1:]:
            c = getConstantInt(idx)
            if not c:
                var = self.getOperand(idx)
                assert var, "Unsupported GEP instruction"
                assert idx is operands[-1], "Variable in the middle of GEP is unsupported now"
                M = Mul(var, Constant(elemSize, SizeType))
                varIdx.append(M)
                if shift != 0:
                    varIdx.append(Add(M, Constant(shift, SizeType)))
            else:
                shift += c.getValue() * elemSize

            if isPointerTy(ty):
                ty = ty.element_type
            elif isArrayTy(ty):
                _, ty = parseArrayTy(ty)
            elemSize = getTypeSize(ty)

        mem = self.getOperand(operands[0])

        if varIdx:
                A = Add(mem, varIdx[-1])
                self._addMapping(inst, A)
                varIdx.append(A)
                return varIdx
        else:
            if shift == 0:
                self._addMapping(inst, mem)
                return []
            else:
                A = Add(mem, Constant(shift, SizeType))
                self._addMapping(inst, A)
        return [A]

    def _handlePhi(self, inst):
        operands = getLLVMOperands(inst)
        bnum = getTypeSize(inst.type)
        phivar = Alloc(Constant(bnum, SizeType))
        L = Load(phivar, bnum)
        self._addMapping(inst, L)
        self.phis.append((inst, phivar, L))
        return [L]

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
        elif inst.opcode == 'sext':
            return self._createSExt(inst)
        elif inst.opcode == 'trunc':
            return self._createTrunc(inst)
        elif inst.opcode == 'getelementptr':
            return self._createGep(inst)
        elif inst.opcode == 'bitcast':
            return self._createCast(inst)
        elif inst.opcode in ['add', 'sub', 'div', 'mul', 'udiv']:
            return self._createArith(inst, inst.opcode)
        elif inst.opcode in ['shl', 'lshr', 'ashr']:
            return self._createShift(inst)
        elif inst.opcode in ['and', 'or', 'xor']:
            return self._createLogicOp(inst)
        elif inst.opcode in ['srem', 'urem']:
            return self._createRem(inst)
        elif inst.opcode == 'phi':
            return self._handlePhi(inst)
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
                assert inst.opcode in ['bitcast', 'call', 'getelementptr'] or instrs,\
                       "No instruction was created"
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

        # finish PHI nodes
        if self.phis:
            print_stderr("PHI nodes yet not supported", color="RED")
            exit(1)
       #for inst, var, load in self.phis:
       #    operands = getLLVMOperands(inst)


    def _parse_module(self, m):
        #XXX globals!

        # create the function at first,
        # because they may be operands of calls
        for f in m.functions:
            assert f.type.is_pointer, "Function pointer type is not a pointer"
            succ, retty = parseFunctionRetTy(f.type.element_type)
            if not succ:
                raise NotImplementedError("Cannot parse function return type: {0}".format(f.type.element_type))
            self.program.addFun(Function(f.name, len(list(f.arguments)), retty))

        for f in m.functions:
            self._parse_fun(f)

    def _parse(self, path):
        m = _get_llvm_module(path)
        self._parse_module(m)

        # FIXME: set entry here?

        return self.program

    def parse(self, path):
        return self._parse(path)
if __name__ == "__main__":
    from sys import argv
    parser = Parser()
    P = parser.parse(argv[1])
    P.dump()

