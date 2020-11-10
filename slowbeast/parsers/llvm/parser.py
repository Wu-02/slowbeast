from slowbeast.domains.concrete import ConcreteVal, ConcreteInt
from slowbeast.ir.program import Program
from slowbeast.ir.function import Function

from slowbeast.ir.types import *
from slowbeast.ir.instruction import *

from slowbeast.util.debugging import print_stderr

from .specialfunctions import special_functions, create_special_fun
from .utils import *

import llvmlite.binding as llvm


def _get_llvm_module(path):
    if path.endswith(".ll"):
        with open(path, "rt") as f:
            return llvm.parse_assembly(f.read())
    else:
        with open(path, "rb") as f:
            return llvm.parse_bitcode(f.read())


def parseCmp(inst):
    parts = str(inst).split()
    if parts[1] != "=" and parts[2] != "icmp":
        return None, False

    if parts[3] == "eq":
        return Cmp.EQ, False
    elif parts[3] == "ne":
        return Cmp.NE, False
    elif parts[3] == "le" or parts[3] == "sle":
        return Cmp.LE, False
    elif parts[3] == "ge" or parts[3] == "sge":
        return Cmp.GE, False
    elif parts[3] == "lt" or parts[3] == "slt":
        return Cmp.LT, False
    elif parts[3] == "gt" or parts[3] == "sgt":
        return Cmp.GT, False
    elif parts[3] == "ule":
        return Cmp.LE, True
    elif parts[3] == "uge":
        return Cmp.GE, True
    elif parts[3] == "ult":
        return Cmp.LT, True
    elif parts[3] == "ugt":
        return Cmp.GT, True

    else:
        return None, False


def parseFunctionRetTy(ty):
    parts = str(ty).split()
    if len(parts) < 2:
        return False, None
    if parts[0] == "void":
        return True, None
    else:
        sz = type_size_in_bits(parts[0])
        if sz:
            return True, IntType(sz)
    return False, None


def countSyms(s, sym):
    cnt = 0
    for x in s:
        if x == sym:
            cnt += 1
    return cnt


class Parser:
    def __init__(self):
        self.program = Program()
        self._bblocks = {}
        self._mapping = {}
        self._metadata_opts = ["llvm"]
        # records about PHIs that we created. We must place
        # the writes emulating PHIs only after all blocks were created.
        self.phis = []

    def getOperand(self, op):
        ret = self._mapping.get(op)
        if not ret:
            ret = getConstantInt(op)
        if not ret:
            ret = getConstantPtr(op)

        assert ret, "Do not have an operand: {0}".format(op)
        return ret

    def getBBlock(self, llvmb):
        return self._bblocks[llvmb]

    def fun(self, fn):
        return self.program.fun(fn)

    def _addMapping(self, llinst, sbinst):
        if "llvm" in self._metadata_opts:
            sbinst.addMetadata("llvm", str(llinst))
        assert self._mapping.get(llinst) is None, "Duplicated mapping"
        self._mapping[llinst] = sbinst

    def _createAlloca(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Array allocations not supported yet"

        tySize = type_size(inst.type.element_type)
        assert tySize and tySize > 0, "Invalid type size"
        num = self.getOperand(operands[0])

        if isinstance(num, ValueInstruction):  # VLA
            retlist = []
            bytewidth = type_size(operands[0].type)
            if bytewidth != SizeType.bytewidth():
                N = ZExt(num, ConcreteVal(SizeType.bitwidth(), SizeType))
                retlist.append(N)
            else:
                N = num
            M = Mul(ConcreteVal(tySize, SizeType), N)
            A = Alloc(M)
            self._addMapping(inst, A)
            retlist += [M, A]
            return retlist
        else:
            A = Alloc(ConcreteInt(tySize * num.value(), num.bitwidth()))
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

        bytesNum = type_size(inst.type)
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
        if opcode == "add":
            I = Add(op1, op2)
        elif opcode == "sub":
            I = Sub(op1, op2)
        elif opcode == "mul":
            I = Mul(op1, op2)
        elif opcode == "sdiv":
            I = Div(op1, op2)
        elif opcode == "udiv":
            I = Div(op1, op2, unsigned=True)
        else:
            raise NotImplementedError(
                "Artihmetic operation unsupported: {0}".format(inst)
            )

        self._addMapping(inst, I)
        return [I]

    def _createShift(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for shift"

        op1 = self.getOperand(operands[0])
        op2 = self.getOperand(operands[1])
        opcode = inst.opcode

        if opcode == "shl":
            I = Shl(op1, op2)
        elif opcode == "lshr":
            I = LShr(op1, op2)
        elif opcode == "ashr":
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

        if opcode == "and":
            I = And(op1, op2)
        elif opcode == "or":
            I = Or(op1, op2)
        elif opcode == "xor":
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

        if opcode == "srem":
            I = Rem(op1, op2)
        elif opcode == "urem":
            I = Rem(op1, op2, unsigned=True)
        else:
            raise NotImplementedError(
                "Remainder operation unsupported: {0}".format(inst)
            )

        self._addMapping(inst, I)
        return [I]

    def _createCmp(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 2, "Invalid number of operands for cmp"
        P, is_unsigned = parseCmp(inst)
        if not P:
            raise NotImplementedError("Unsupported cmp instruction: {0}".format(inst))

        C = Cmp(
            P, self.getOperand(operands[0]), self.getOperand(operands[1]), is_unsigned
        )
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
        mp, seq = create_special_fun(self, inst, fun)
        if mp:
            self._addMapping(inst, mp)
        return seq

    def _createCall(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) > 0

        # uffff, llvmlite really sucks in parsing LLVM.
        # We cannot even get constantexprs...
        fun = operands[-1].name
        if not fun:
            sop = str(operands[-1])
            if "bitcast" in sop:
                for x in sop.split():
                    if x[0] == "@":
                        fun = x[1:]
                        if self.fun(fun):
                            break
                        else:
                            fun = None
        if not fun:
            raise NotImplementedError("Unsupported call: {0}".format(inst))

        if fun.startswith("llvm.dbg"):
            return []

        if fun in special_functions:
            return self._createSpecialCall(inst, fun)

        F = self.fun(fun)
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
        zext = ZExt(
            self.getOperand(operands[0]),
            ConcreteInt(type_size_in_bits(inst.type), 32),
        )
        self._addMapping(inst, zext)
        return [zext]

    def _createSExt(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        sext = SExt(
            self.getOperand(operands[0]),
            ConcreteInt(type_size_in_bits(inst.type), 32),
        )
        self._addMapping(inst, sext)
        return [sext]

    def _createTrunc(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        bits = type_size_in_bits(inst.type)
        ext = ExtractBits(
            self.getOperand(operands[0]),
            ConcreteInt(0, 32),
            ConcreteInt(bits - 1, 32),
        )
        self._addMapping(inst, ext)
        return [ext]

    def _createCast(self, inst):
        operands = getLLVMOperands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        bits = type_size_in_bits(inst.type)
        op = self.getOperand(operands[0])
        if op.is_concrete():
            self._mapping[inst] = op
            return []
        elif is_pointer_ty(operands[0].type):
            self._addMapping(inst, self.getOperand(operands[0]))
            return []
        else:
            raise NotImplementedError("Unhandled cast: {0}".format(inst))

    def _createGep(self, inst):
        operands = getLLVMOperands(inst)
        assert is_pointer_ty(operands[0].type), "First type of GEP is not a pointer"
        ty = operands[0].type.element_type
        elemSize = type_size(ty)
        shift = 0
        varIdx = []
        for idx in operands[1:]:
            c = getConstantInt(idx)
            if not c:
                var = self.getOperand(idx)
                assert var, "Unsupported GEP instruction"
                assert (
                    idx is operands[-1]
                ), "Variable in the middle of GEP is unsupported now"
                mulbw = type_size_in_bits(idx.type)
                assert 0 < mulbw <= 64, "Invalid type size: {mulbw}"
                if mulbw != SizeType.bitwidth():
                    C = ZExt(var, ConcreteVal(SizeType.bitwidth(), SizeType))
                    varIdx.append(C)
                    var = C
                M = Mul(var, ConcreteVal(elemSize, SizeType))
                varIdx.append(M)
                if shift != 0:
                    varIdx.append(Add(M, ConcreteVal(shift, SizeType)))
            else:
                shift += c.value() * elemSize

            if is_pointer_ty(ty) or is_array_ty(ty):
                ty = ty.element_type
            elemSize = type_size(ty)

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
                A = Add(mem, ConcreteVal(shift, SizeType))
                self._addMapping(inst, A)
        return [A]

    def _handlePhi(self, inst):
        operands = getLLVMOperands(inst)
        bnum = type_size(inst.type)
        phivar = Alloc(ConcreteVal(bnum, SizeType))
        L = Load(phivar, bnum)
        self._addMapping(inst, L)
        self.phis.append((inst, phivar, L))
        return [L]

    def _parse_instruction(self, inst):
        if inst.opcode == "alloca":
            return self._createAlloca(inst)
        elif inst.opcode == "store":
            return self._createStore(inst)
        elif inst.opcode == "load":
            return self._createLoad(inst)
        elif inst.opcode == "ret":
            return self._createRet(inst)
        elif inst.opcode == "icmp":
            return self._createCmp(inst)
        elif inst.opcode == "br":
            return self._createBranch(inst)
        elif inst.opcode == "call":
            return self._createCall(inst)
        elif inst.opcode == "unreachable":
            return self._createUnreachable(inst)
        elif inst.opcode == "zext":
            return self._createZExt(inst)
        elif inst.opcode == "sext":
            return self._createSExt(inst)
        elif inst.opcode == "trunc":
            return self._createTrunc(inst)
        elif inst.opcode == "getelementptr":
            return self._createGep(inst)
        elif inst.opcode == "bitcast":
            return self._createCast(inst)
        elif inst.opcode in ["add", "sub", "sdiv", "mul", "udiv"]:
            return self._createArith(inst, inst.opcode)
        elif inst.opcode in ["shl", "lshr", "ashr"]:
            return self._createShift(inst)
        elif inst.opcode in ["and", "or", "xor"]:
            return self._createLogicOp(inst)
        elif inst.opcode in ["srem", "urem"]:
            return self._createRem(inst)
        elif inst.opcode == "phi":
            return self._handlePhi(inst)
        else:
            raise NotImplementedError("Unsupported instruction: {0}".format(inst))

    def _parse_block(self, F, block):
        """
        F     - slowbeast.Function
        block - llvm.block
        """
        B = self.getBBlock(block)
        assert B is not None, "Do not have a bblock"

        for inst in block.instructions:
            # the result of parsing one llvm instruction
            # may be several slowbeast instructions
            try:
                instrs = self._parse_instruction(inst)
                assert (
                    inst.opcode in ["bitcast", "call", "getelementptr"] or instrs
                ), "No instruction was created"
                for I in instrs:
                    B.append(I)
            except Exception as e:
                print_stderr(
                    "Failed parsing llvm while parsing: {0}".format(inst), color="RED"
                )
                raise e

        assert B.fun() is F

    def _parse_fun(self, f):
        F = self.fun(f.name)

        # add mapping to arguments of the function
        for n, a in enumerate(f.arguments):
            self._addMapping(a, F.getArgument(n))

        # first create blocks as these can be operands to br instructions
        for b in f.blocks:
            self._bblocks[b] = BBlock(F)

        # now create the contents of the blocks
        for b in f.blocks:
            self._parse_block(F, b)

        # place the rest of instructions simulating PHI nodes
        if self.phis:
            for inst, var, load in self.phis:
                # place the allocation to the entry node
                var.insertBefore(F.getBBlock(0).last())
                # place the writes to memory
                for i in range(0, inst.phi_incoming_count):
                    v, b = inst.phi_incoming(i)
                    B = self._bblocks[b]
                    S = Store(self.getOperand(v), var)
                    S.insertBefore(B.last())
            self.phis = []  # we handled these PHI nodes

    def _parse_globals(self, m):
        for g in m.global_variables:
            assert g.type.is_pointer
            # FIXME: check and set whether it is a constant
            ts = type_size(g.type.element_type)
            assert ts is not None, "Unsupported type size: {g.type.element_type}"
            G = GlobalVariable(ConcreteVal(ts, SizeType), g.name)
            c = getConstantInt(g.initializer)
            if c:
                # FIXME: add composed instruction
                G.setInit([Store(c, G)])
            # elif is_array_ty(g.initializer.type):
            #    parts=str(g.initializer.type).split()
            #    assert parts[1] == 'x'
            #    if parts[2].startswith('i'):
            #        print(parts)
            #    # FIXME: add String type to represent strings
            else:
                print_stderr(
                    "Unsupported initializer: {0}".format(g.initializer), color="YELLOW"
                )
            self.program.add_global(G)
            self._addMapping(g, G)

    def _parse_module(self, m):
        self._parse_globals(m)

        # create the function at first,
        # because they may be operands of calls
        for f in m.functions:
            assert f.type.is_pointer, "Function pointer type is not a pointer"
            succ, retty = parseFunctionRetTy(f.type.element_type)
            if not succ:
                raise NotImplementedError(
                    "Cannot parse function return type: {0}".format(f.type.element_type)
                )
            self.program.addFun(Function(f.name, len(list(f.arguments)), retty))

        for f in m.functions:
            if f.name in special_functions:
                # do not build these as we will replace their
                # calls with our stubs anyway
                continue

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
