from typing import Any, Iterable, Tuple

import llvmlite.binding as llvm

from slowbeast.ir.argument import Argument
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import *
from slowbeast.ir.program import Program
from slowbeast.ir.programelement import ProgramElement
from slowbeast.ir.types import *
from slowbeast.util.debugging import print_stderr
from .specialfunctions import (
    special_functions,
    create_special_fun,
    modelled_functions,
    try_model_function,
)
from .utils import *

concrete_value = ConcreteDomain.get_value


def _get_llvm_module(path: str) -> ModuleRef:
    if path.endswith(".ll"):
        with open(path, "rt") as f:
            return llvm.parse_assembly(f.read())
    else:
        with open(path, "rb") as f:
            return llvm.parse_bitcode(f.read())


def parse_special_fcmp(inst, op1, op2, optypes):
    seq = []
    parts = str(inst).split()
    if parts[1] != "=":
        return None, False

    if parts[2] != "fcmp":
        return None, False

    if parts[3] == "uno":
        if op1 == op2:
            # equivalent to isnan
            return [FpOp(FpOp.IS_NAN, op1, optypes[0])]
        seq.append(FpOp(FpOp.IS_NAN, op1, optypes[0]))
        seq.append(FpOp(FpOp.IS_NAN, op2, optypes[1]))
        seq.append(BinaryOperation(BinaryOperation.AND, *seq, [BoolType()] * 2))
        return seq
    if parts[3] == "ord":
        if op1 == op2:
            # equivalent to not isnan
            seq.append(FpOp(FpOp.IS_NAN, op1, optypes[0]))
            seq.append(Cmp(Cmp.EQ, seq[-1], ConstantFalse, [BoolType] * 2))
        else:
            seq.append(FpOp(FpOp.IS_NAN, op1, optypes[0]))
            seq.append(Cmp(Cmp.EQ, seq[-1], ConstantFalse, [BoolType] * 2))
            seq.append(FpOp(FpOp.IS_NAN, op2, optypes[1]))
            seq.append(Cmp(Cmp.EQ, seq[-1], ConstantFalse, [BoolType] * 2))
            seq.append(
                BinaryOperation(BinaryOperation.AND, seq[1], seq[-1], [BoolType] * 2)
            )
        return seq
    return None


def parse_fcmp(inst: ValueRef) -> Tuple[Optional[int], bool]:
    parts = str(inst).split()
    if parts[1] != "=":
        return None, False

    if parts[2] != "fcmp":
        return None, False

    if parts[3] == "oeq":
        return Cmp.EQ, False
    if parts[3] == "one":
        return Cmp.NE, False
    if parts[3] == "ole":
        return Cmp.LE, False
    if parts[3] == "oge":
        return Cmp.GE, False
    if parts[3] == "olt":
        return Cmp.LT, False
    if parts[3] == "ogt":
        return Cmp.GT, False
    if parts[3] == "ule":
        return Cmp.LE, True
    if parts[3] == "uge":
        return Cmp.GE, True
    if parts[3] == "ult":
        return Cmp.LT, True
    if parts[3] == "ugt":
        return Cmp.GT, True
    if parts[3] == "ueq":
        return Cmp.EQ, True
    if parts[3] == "une":
        return Cmp.NE, True

    return None, False


def parse_cmp(inst) -> Tuple[Optional[int], bool]:
    parts = str(inst).split()
    if parts[1] != "=":
        return None, False

    if parts[2] != "icmp":
        return None, False

    if parts[3] == "eq":
        return Cmp.EQ, False
    if parts[3] == "ne":
        return Cmp.NE, False
    if parts[3] == "le" or parts[3] == "sle":
        return Cmp.LE, False
    if parts[3] == "ge" or parts[3] == "sge":
        return Cmp.GE, False
    if parts[3] == "lt" or parts[3] == "slt":
        return Cmp.LT, False
    if parts[3] == "gt" or parts[3] == "sgt":
        return Cmp.GT, False
    if parts[3] == "ule":
        return Cmp.LE, True
    if parts[3] == "uge":
        return Cmp.GE, True
    if parts[3] == "ult":
        return Cmp.LT, True
    if parts[3] == "ugt":
        return Cmp.GT, True

    return None, False


def parse_fun_ret_ty(
    m: ModuleRef, ty: TypeRef
) -> Tuple[bool, Union[None, FloatType, BitVecType]]:
    parts = str(ty).split()
    if len(parts) < 2:
        return False, None
    if parts[0] == "void":
        return True, None
    elif ty.is_struct:
        sz = type_size_in_bits(m, parts[0])
        return True, type_mgr.bytes_ty(sz)
    else:
        sz = type_size_in_bits(m, parts[0])
        if sz:
            if parts[0] in ("float", "double"):
                return True, type_mgr().float_ty(sz)
            else:
                return True, type_mgr().bv_ty(sz)
    return False, None


def count_symbols(s, sym) -> int:
    cnt = 0
    for x in s:
        if x == sym:
            cnt += 1
    return cnt


def offset_of_struct_elem(llvmmodule, ty, cval) -> int:
    assert ty.is_struct, ty
    assert cval < ty.struct_num_elements
    off = 0
    for i in range(0, cval):
        elemty = ty.struct_element_type(i)
        tysize = type_size(llvmmodule, elemty)
        assert tysize > 0, f"Invalid type size: {tysize}"
        off += tysize

    return off


unsupported_funs = [
    "pthread_get_specific",
    "pthread_set_specific",
    "pthread_cond_signal",
    "pthread_cond_broadcast",
    "pthread_cond_wait",
    "pthread_cond_timedwait",
]
thread_funs = ["pthread_create", "pthread_join", "pthread_exit"]


def arith_nsw_flag(inst):
    # FIXME...
    parts = str(inst).split()
    assert parts[1] == "="
    assert parts[2] in ("add", "sub", "mul")
    return parts[3] == "nsw"


def shl_nsw_flag(inst):
    # FIXME...
    parts = str(inst).split()
    assert parts[1] == "="
    assert parts[2] == "shl"
    return parts[3] == "nsw"


class Parser:
    def __init__(
        self,
        error_funs: None = None,
        allow_threads: bool = True,
        forbid_floats: bool = False,
        unsupp_funs: Optional[Iterable[str]] = None,
        to_check: Optional[Iterable[str]] = None,
    ) -> None:
        self.llvmmodule = None
        self.program = Program()
        self.error_funs = error_funs or []
        self._bblocks = {}
        self._mapping = {}
        self._funs = {}
        self._names = {}
        self._metadata_opts = ["llvm", "dbgloc", "dbgvar"]
        self._name_vars = True
        self._allow_threads = allow_threads
        self._to_check = to_check
        # records about PHIs that we created. We must place
        # the writes emulating PHIs only after all blocks were created.
        self.phis = []
        self._errno_loc = None

        self.current_bblock = None
        self.current_fun = None

        if unsupp_funs:
            global unsupported_funs
            unsupported_funs += unsupp_funs
        self._forbid_floats = forbid_floats

    def try_get_operand(self, op: ValueRef) -> Any:
        ret = self._mapping.get(op)
        if not ret:
            ret = get_constant(op)
        if not ret:
            if op.is_constantexpr:
                ret = self._parse_ce(op)
        if not ret:
            # try if it is a function
            ret = self._funs.get(op)

        return ret

    def operand(self, op: ValueRef) -> Any:
        ret = self.try_get_operand(op)
        assert ret, f"Do not have an operand: {op}"
        return ret

    def bblock(self, llvmb: ValueRef) -> BBlock:
        return self._bblocks[llvmb]

    def fun(self, fn: str) -> Optional[Function]:
        return self.program.fun(fn)

    def _addMapping(self, llinst: ValueRef, sbinst: ProgramElement) -> None:
        if "llvm" in self._metadata_opts:
            sbinst.add_metadata("llvm", str(llinst))
        if "dbgloc" in self._metadata_opts:
            dl = llinst.dbg_loc
            if dl[1] > 0:
                sbinst.add_metadata("dbgloc", dl)
        assert self._mapping.get(llinst) is None, "Duplicated mapping"
        self._mapping[llinst] = sbinst

    def _createAlloca(self, inst: ValueRef) -> list:
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Array allocations not supported yet"

        tySize = type_size(self.llvmmodule, inst.type.element_type)
        assert tySize and tySize > 0, "Invalid type size"
        num = self.operand(operands[0])

        if isinstance(num, ValueInstruction):  # VLA
            retlist = []
            bytewidth = type_size(self.llvmmodule, operands[0].type)
            size_type = get_size_type()
            if bytewidth != size_type.bytewidth():
                N = Extend(num, size_type.bitwidth(), False, [size_type])
                retlist.append(N)
            else:
                N = num

            M = BinaryOperation(
                BinaryOperation.MUL,
                concrete_value(tySize, size_type),
                N,
                [size_type, N.type()],
            )
            A = Alloc(M)
            self._addMapping(inst, A)
            retlist += [M, A]
            return retlist
        else:
            A = Alloc(concrete_value(tySize * num.value(), num.bitwidth()))
            self._addMapping(inst, A)
            return [A]

    def _createStore(self, inst: ValueRef) -> List[Store]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for store"

        S = Store(
            self.operand(operands[0]),
            self.operand(operands[1]),
            [get_sb_type(self.llvmmodule, op.type) for op in operands],
        )
        self._addMapping(inst, S)
        return [S]

    def _createLoad(self, inst: ValueRef) -> List[Load]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"

        L = Load(
            self.operand(operands[0]),
            get_sb_type(self.llvmmodule, inst.type),
            [get_sb_type(self.llvmmodule, operands[0].type)],
        )
        self._addMapping(inst, L)
        return [L]

    def _createRet(
        self, inst: ValueRef
    ) -> Union[List[Return], List[Union[None, Call, Return]]]:
        operands = get_llvm_operands(inst)
        assert len(operands) <= 1, "Invalid number of operands for ret"

        if len(operands) == 0:
            R = Return()
        else:
            op = self.try_get_operand(operands[0])
            if op is None:
                # uhhh, hack...)
                if str(operands[0]).endswith("undef"):
                    ty = operands[0].type
                    op = self.create_nondet_call(f"undef_{ty}".replace(" ", "_"), ty)
                else:
                    raise RuntimeError(f"Unhandled instruction: {inst}")
                R = Return(op, get_sb_type(self.llvmmodule, operands[0].type))
                self._addMapping(inst, R)
                return [op, R]
            else:
                R = Return(op, get_sb_type(self.llvmmodule, operands[0].type))

        self._addMapping(inst, R)
        return [R]

    def _createArith(self, inst, opcode) -> List[BinaryOperation]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for store"

        op1 = self.operand(operands[0])
        op2 = self.operand(operands[1])
        isfloat = False
        if opcode.startswith("f"):
            op1 = to_float_ty(op1)
            op2 = to_float_ty(op2)
            isfloat = True
        if isfloat and self._forbid_floats:
            raise RuntimeError(f"Floating artihmetic forbidden: {inst}")

        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands]
        if opcode in ("add", "fadd"):
            I = BinaryOperation(BinaryOperation.ADD, op1, op2, optypes)
        elif opcode in ("sub", "fsub"):
            I = BinaryOperation(BinaryOperation.SUB, op1, op2, optypes)
        elif opcode in ("mul", "fmul"):
            I = BinaryOperation(BinaryOperation.MUL, op1, op2, optypes)
        elif opcode in ("sdiv", "fdiv"):
            I = BinaryOperation(BinaryOperation.DIV, op1, op2, optypes)
        elif opcode == "udiv":
            I = BinaryOperation(BinaryOperation.UDIV, op1, op2, optypes)
        else:
            raise NotImplementedError(f"Artihmetic operation unsupported: {inst}")

        self._addMapping(inst, I)
        if opcode in ("add", "mul", "sub") and arith_nsw_flag(inst):
            chck = self._create_overflow_check(I)
            if chck:
                return chck + [I]
        return [I]

    def _create_overflow_check(self, I):
        if self._to_check is None or "no-overflow" not in self._to_check:
            return None
        ty = I.type()
        if not ty.is_bv():
            return None

        op = I.operation()
        if op == BinaryOperation.ADD:
            OCHK = IntOp(
                IntOp.ADD_DONT_OVERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            OA = Assert(OCHK, "add: signed integer overflow")
            UCHK = IntOp(
                IntOp.ADD_DONT_UNDERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            UA = Assert(UCHK, "add: signed integer underflow")
            return [OCHK, OA, UCHK, UA]
        if op == BinaryOperation.SUB:
            OCHK = IntOp(
                IntOp.SUB_DONT_OVERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            OA = Assert(OCHK, "sub: signed integer overflow")
            UCHK = IntOp(
                IntOp.SUB_DONT_UNDERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            UA = Assert(UCHK, "sub: signed integer underflow")
            return [OCHK, OA, UCHK, UA]
        if op == BinaryOperation.MUL:
            OCHK = IntOp(
                IntOp.MUL_DONT_OVERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            OA = Assert(OCHK, "mul: signed integer overflow")
            UCHK = IntOp(
                IntOp.MUL_DONT_UNDERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            UA = Assert(UCHK, "mul: signed integer underflow")
            return [OCHK, OA, UCHK, UA]
        if op == BinaryOperation.DIV:
            CHK = IntOp(
                IntOp.DIV_DONT_OVERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            A = Assert(CHK, "div: signed integer overflow")
            return [CHK, A]
        if op == BinaryOperation.SHL:
            CHK = IntOp(
                IntOp.SHL_DONT_OVERFLOW,
                I.operands(),
                [op.type() for op in I.operands()],
            )
            A = Assert(CHK, "shl: signed integer overflow")
            return [CHK, A]
        raise NotImplementedError(f"Checking overflow of {I} is not implemented")

    def _createShift(self, inst) -> List[BinaryOperation]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for shift"

        op1 = self.operand(operands[0])
        op2 = self.operand(operands[1])
        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands]
        opcode = inst.opcode

        if opcode == "shl":
            I = BinaryOperation(BinaryOperation.SHL, op1, op2, optypes)
        elif opcode == "lshr":
            I = BinaryOperation(BinaryOperation.LSHR, op1, op2, optypes)
        elif opcode == "ashr":
            I = BinaryOperation(BinaryOperation.ASHR, op1, op2, optypes)
        else:
            raise NotImplementedError(f"Shift operation unsupported: {inst}")

        self._addMapping(inst, I)
        if opcode == "shl":  # and shl_nsw_flag(inst):
            chck = self._create_overflow_check(I)
            if chck:
                return chck + [I]
        return [I]

    def _createLogicOp(self, inst) -> List[BinaryOperation]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for logic op"

        op1 = self.operand(operands[0])
        op2 = self.operand(operands[1])
        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands]
        opcode = inst.opcode

        casts = []
        if op1.type().bitwidth() == 1:
            assert op2.type().bitwidth() == 1, op2
            if op1.type().is_bool() and not op2.type().is_bool():
                op2 = Cast(op2, type_mgr().bool_ty(), False, [type_mgr().bool_ty()])
                casts.append(op2)
            elif not op1.type().is_bool() and op2.type().is_bool():
                op1 = Cast(op1, type_mgr().bool_ty(), False, [type_mgr().bool_ty()])
                casts.append(op1)

        # make sure both operands are bool if one is bool
        # if op1.type().is_bool() or op2.type().is_bool():
        #    op1, op2 = bv_to_bool_else_id(op1), bv_to_bool_else_id(op2)

        if opcode == "and":
            I = BinaryOperation(BinaryOperation.AND, op1, op2, optypes)
        elif opcode == "or":
            I = BinaryOperation(BinaryOperation.OR, op1, op2, optypes)
        elif opcode == "xor":
            I = BinaryOperation(BinaryOperation.XOR, op1, op2, optypes)
        else:
            raise NotImplementedError(f"Logic operation unsupported: {inst}")

        self._addMapping(inst, I)
        return casts + [I]

    def _createSelect(self, inst) -> List[Ite]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 3, "Invalid number of operands for select"

        cond = self.operand(operands[0])
        op1 = self.operand(operands[1])
        op2 = self.operand(operands[2])
        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands[1:]]

        I = Ite(cond, op1, op2, optypes)
        self._addMapping(inst, I)
        return [I]

    def _createRem(self, inst) -> List[BinaryOperation]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for rem"

        op1 = self.operand(operands[0])
        op2 = self.operand(operands[1])
        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands]
        opcode = inst.opcode

        if opcode == "srem":
            I = BinaryOperation(BinaryOperation.REM, op1, op2, optypes)
        elif opcode == "urem":
            I = BinaryOperation(BinaryOperation.UREM, op1, op2, optypes)
        else:
            raise NotImplementedError(f"Remainder operation unsupported: {inst}")

        self._addMapping(inst, I)
        return [I]

    def _createFNeg(self, inst) -> List[Neg]:
        if self._forbid_floats:
            raise RuntimeError(f"Floating operations forbidden: {inst}")

        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for fneg"
        I = Neg(
            to_float_ty(self.operand(operands[0])),
            get_sb_type(self.llvmmodule, inst.type),
            [get_sb_type(self.llvmmodule, operands[0].type)],
        )
        self._addMapping(inst, I)
        return [I]

    def _createCmp(self, inst: ValueRef, isfloat: bool = False) -> List[Cmp]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 2, "Invalid number of operands for cmp"
        op1 = self.operand(operands[0])
        op2 = self.operand(operands[1])
        optypes = [get_sb_type(self.llvmmodule, op.type) for op in operands]
        if isfloat:
            if self._forbid_floats:
                raise RuntimeError(f"Floating operations forbidden: {inst}")

            P, is_unordered = parse_fcmp(inst)
            op1 = to_float_ty(op1)
            op2 = to_float_ty(op2)
            if not P:
                seq = parse_special_fcmp(inst, op1, op2)
                if seq:
                    self._addMapping(inst, seq[-1])
                    return seq
                raise NotImplementedError(f"Unsupported fcmp instruction: {inst}")
            C = Cmp(P, op1, op2, optypes, is_unordered)
        else:
            P, is_unsigned = parse_cmp(inst)
            if not P:
                raise NotImplementedError(f"Unsupported cmp instruction: {inst}")
            C = Cmp(P, op1, op2, optypes, is_unsigned)

        self._addMapping(inst, C)
        return [C]

    def _createBranch(self, inst: ValueRef) -> List[Branch]:
        operands = get_llvm_operands(inst)
        if len(operands) == 3:
            cond = self.operand(operands[0])
            # XXX: whaat? for some reason, the bindings return
            # the false branch as first
            b1 = self.bblock(operands[2])
            b2 = self.bblock(operands[1])
            B = Branch(cond, b1, b2)
        elif len(operands) == 1:
            b1 = self.bblock(operands[0])
            B = Branch(ConstantTrue, b1, b1)
        else:
            raise NotImplementedError("Invalid number of operands for br")
        self._addMapping(inst, B)
        return [B]

    def _handleSwitch(self, inst) -> List[Switch]:
        toop = self.operand
        tobb = self.bblock
        operands = get_llvm_operands(inst)
        S = Switch(
            toop(operands[0]),
            tobb(operands[1]),
            [
                (toop(operands[i]), tobb(operands[i + 1]))
                for i in range(2, len(operands), 2)
            ],
        )
        self._addMapping(inst, S)
        return [S]

    def create_nondet_call(self, name, ty) -> Call:
        fun = self._funs.get(name)
        if fun is None:
            fun = Function(name, [], ty)
            self.program.add_fun(fun)

        return Call(fun, ty, [], [])

    def _createSpecialCall(self, inst: ValueRef, fun: str) -> List[Assert]:
        mp, seq = create_special_fun(self, inst, fun, self.error_funs, self._to_check)
        if mp:
            self._addMapping(inst, mp)
        return seq

    def _try_model_function(self, inst: ValueRef, fun: str):
        mp, seq = try_model_function(self, inst, fun, self.error_funs, self._to_check)
        if mp:
            self._addMapping(inst, mp)
        return seq

    def _createThreadFun(self, inst, operands: list, fun):
        if fun == "pthread_join":
            assert len(operands) == 3  # +1 for called fun
            ty = get_sb_type(self.llvmmodule, operands[1].type.element_type)
            # FIXME: we do not condition joining the thread on 'ret'...
            succ = self.create_nondet_call(
                "__join_succeeded", get_sb_type(self.llvmmodule, inst.type)
            )
            t = ThreadJoin(
                ty,
                [self.operand(operands[0])],
                [get_sb_type(self.llvmmodule, operands[0].type)],
            )
            self._addMapping(inst, succ)
            ret = self.operand(operands[1])
            if ret.is_concrete() and ret.is_null():
                return [succ, t]
            s = Store(t, ret, type_mgr().pointer_ty())
            return [succ, t, s]
        if fun == "pthread_create":
            assert len(operands) == 5  # +1 for called fun
            # FIXME: we do not condition creating the thread on 'ret'...
            ret = self.create_nondet_call(
                "__thread_create_succeeded", get_sb_type(self.llvmmodule, inst.type)
            )
            t = Thread(
                self.operand(operands[2]),
                [self.operand(operands[3])],
                [get_sb_type(self.llvmmodule, operands[3].type)],
            )
            s = Store(
                t,
                self.operand(operands[0]),
                [t.type(), get_sb_type(self.llvmmodule, operands[0].type)],
            )
            self._addMapping(inst, ret)
            return [ret, t, s]
        if fun == "pthread_exit":
            assert len(operands) == 2  # +1 for called fun
            t = Return(
                self.operand(operands[0]),
                get_sb_type(self.llvmmodule, operands[0].type),
            )
            self._addMapping(inst, t)
            return [t]

        raise NotImplementedError(f"Unsupported thread function: {fun}")

    def _createCall(self, inst: ValueRef) -> List[Union[Any, Call, Assert]]:
        operands = get_llvm_operands(inst)
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
            if " asm " in sop:
                return self._handleAsm(inst)
        if not fun:
            op = self.try_get_operand(operands[-1])
            if op is None:
                raise NotImplementedError(f"Unsupported call: {inst}")
            # function pointer call
            ty = get_sb_type(self.llvmmodule, inst.type)
            args = operands[:-1]
            C = Call(
                op,
                ty,
                [self.operand(x) for x in args],
                [get_sb_type(self.llvmmodule, op.type) for op in args],
            )
            self._addMapping(inst, C)
            return [C]

        if fun.startswith("llvm.dbg"):
            if (
                fun in ("llvm.dbg.declare", "llvm.dbg.value")
                and "dbgvar" in self._metadata_opts
            ):
                var, name, ty = llvm.parse_dbg_declare(inst)
                if str(var).endswith(" undef"):
                    return []
                varop = self.operand(var)
                if isinstance(varop, ConcreteVal):
                    return []
                varop.add_metadata(
                    "dbgvar",
                    (name.decode("utf-8", "ignore"), ty.decode("utf-8", "ignore")),
                )
                if self._name_vars:
                    cnt = self._names.setdefault(name, None)
                    if cnt is None:
                        self._names[name] = 0
                        varop.set_name(name.decode("utf-8", "ignore"))
                    else:
                        self._names[name] += 1
                        varop.set_name(f"{name.decode('utf-8', 'ignore')}_{cnt + 1}")
            return []

        if fun in unsupported_funs:
            raise NotImplementedError(f"Unsupported function: {fun}")

        if fun in thread_funs:
            if self._allow_threads:
                return self._createThreadFun(inst, operands, fun)
            raise NotImplementedError(f"Threads are forbiden: {fun}")

        if fun in special_functions or fun in self.error_funs:
            return self._createSpecialCall(inst, fun)

        if fun in modelled_functions:
            seq = self._try_model_function(inst, fun)
            if seq:
                return seq

        F = self.fun(fun)
        if not F:
            raise NotImplementedError(f"Unknown function: {fun}")

        ty = get_sb_type(self.llvmmodule, inst.type)
        args = operands[:-1]
        C = Call(
            F,
            ty,
            [self.operand(x) for x in args],
            [get_sb_type(self.llvmmodule, op.type) for op in args],
        )
        self._addMapping(inst, C)
        return [C]

    def _handleAsm(self, inst) -> List[Call]:
        ty = inst.type
        print_stderr(
            f"Unsupported ASM, taking as noop with nondet return value:", color="yellow"
        )
        print_stderr(str(inst))
        C = self.create_nondet_call(f"asm_{ty}".replace(" ", "_"), ty)
        self._addMapping(inst, C)
        return [C]

    def _createUnreachable(self, inst: ValueRef) -> List[Assert]:
        A = Assert(ConstantFalse, "unreachable")
        self._addMapping(inst, A)
        return [A]

    def _createExt(self, inst, signed) -> List[Extend]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        ret = []
        op = self.operand(operands[0])
        if (
            op.type().is_bool()
        ):  # LLVM does not make difference between i1 and bool, but we do, so do a cast if we got bool to extend
            op = Cast(op, type_mgr().bv_ty(1), False, [op.type()])
            ret.append(op)
        ext = Extend(
            op,
            type_size_in_bits(self.llvmmodule, inst.type),
            signed,  # signed
            [get_sb_type(self.llvmmodule, op.type) for op in operands],
        )
        ret.append(ext)
        self._addMapping(inst, ext)
        return ret

    def _createReinterpCast(self, inst: ValueRef, sgn: bool) -> List[Cast]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for cast"
        insttype = inst.type
        ty = None
        # FIXME: hardcoded bitwidth
        # FIXME: parsing string...
        stype = str(insttype)
        if stype == "float":
            ty = type_mgr().float_ty(32)
        elif stype == "double":
            ty = type_mgr().float_ty(64)
        elif stype == "i8":
            ty = type_mgr().bv_ty(8)
        elif stype == "i16":
            ty = type_mgr().bv_ty(16)
        elif stype == "i32":
            ty = type_mgr().bv_ty(32)
        elif stype == "i64":
            ty = type_mgr().bv_ty(64)
        else:
            raise NotImplementedError(f"Unimplemented cast: {inst}")
        # just behave that there's no ZExt for now
        cast = Cast(
            self.operand(operands[0]),
            ty,
            sgn,
            [get_sb_type(self.llvmmodule, operands[0].type)],
        )
        self._addMapping(inst, cast)
        return [cast]

    def _createPtrToInt(self, inst):
        return self._createCast(inst)

    def _createIntToPtr(self, inst):
        return self._createCast(inst)

    def _createTrunc(self, inst) -> List[ExtractBits]:
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for load"
        # just behave that there's no ZExt for now
        bits = type_size_in_bits(self.llvmmodule, inst.type)
        ext = ExtractBits(
            self.operand(operands[0]),
            0,
            bits - 1,
            [get_sb_type(self.llvmmodule, op.type) for op in operands],
        )
        self._addMapping(inst, ext)
        return [ext]

    def _createCast(self, inst):
        operands = get_llvm_operands(inst)
        assert len(operands) == 1, "Invalid number of operands for cast"
        op = self.operand(operands[0])
        self._mapping[inst] = op
        return []

    def _parseGep(self, inst):
        operands = get_llvm_operands(inst)
        assert is_pointer_ty(operands[0].type), "First type of GEP is not a pointer"
        ty = operands[0].type
        shift = 0
        varIdx = []
        for idx in operands[1:]:
            c = get_constant(idx)
            if not c:
                var = self.operand(idx)
                assert var, "Unsupported GEP instruction"
                if idx is not operands[-1]:
                    raise NotImplementedError(
                        "Variable in the middle of GEP is unsupported now"
                    )

                mulbw = type_size_in_bits(self.llvmmodule, idx.type)
                assert 0 < mulbw <= 64, "Invalid type size: {mulbw}"
                size_type = get_size_type()
                if mulbw != size_type.bitwidth():
                    C = Extend(var, size_type.bitwidth(), True, [size_type])
                    varIdx.append(C)
                    var = C

                # structs are always accessed by constant indices
                assert ty.is_pointer or ty.is_array
                ty = ty.element_type
                elemSize = type_size(self.llvmmodule, ty)

                M = BinaryOperation(
                    BinaryOperation.MUL,
                    var,
                    concrete_value(elemSize, size_type),
                    [type_mgr().pointer_ty(), size_type],
                )
                varIdx.append(M)
                if shift != 0:
                    varIdx.append(
                        BinaryOperation(
                            BinaryOperation.ADD,
                            M,
                            concrete_value(shift, size_type),
                            [type_mgr().pointer_ty(), size_type],
                        )
                    )
            else:
                assert c.is_bv(), f"Invalid GEP index: {c}"
                cval = c.value()
                if ty.is_pointer or ty.is_array:
                    ty = ty.element_type
                    elemSize = type_size(self.llvmmodule, ty)
                    shift += cval * elemSize
                elif ty.is_struct:
                    shift += offset_of_struct_elem(self.llvmmodule, ty, cval)
                    ty = ty.struct_element_type(cval)
                else:
                    raise NotImplementedError(f"Invalid GEP type: {ty}")

        mem = self.operand(operands[0])
        return mem, shift, varIdx

    def _createGep(self, inst):
        mem, shift, varIdx = self._parseGep(inst)

        if varIdx:
            A = BinaryOperation(
                BinaryOperation.ADD,
                mem,
                varIdx[-1],
                [type_mgr().pointer_ty(), get_size_type()],
            )
            self._addMapping(inst, A)
            varIdx.append(A)
            return varIdx
        else:
            if shift == 0:
                self._addMapping(inst, mem)
                return []
            else:
                A = BinaryOperation(
                    BinaryOperation.ADD,
                    mem,
                    concrete_value(shift, get_size_type_size()),
                    [type_mgr().pointer_ty(), get_size_type()],
                )
                self._addMapping(inst, A)
        return [A]

    def _createCEGep(self, inst):
        mem, shift, varIdx = self._parseGep(inst)
        assert not varIdx, "CE GEP has variable indexes"
        if shift == 0:
            return mem
        else:
            return BinaryOperation(
                BinaryOperation.ADD,
                mem,
                concrete_value(shift, get_size_type()),
                [type_mgr().pointer_ty(), get_size_type()],
            )

    def _parse_ce(self, ce):
        assert ce.is_constantexpr, ce
        # FIXME: we leak the instruction created from CE
        inst = ce.ce_as_inst
        opcode = inst.opcode
        if opcode == "getelementptr":
            return self._createCEGep(inst)
        if opcode in ("bitcast", "ptrtoint", "inttoptr"):
            operands = get_llvm_operands(inst)
            assert len(operands) == 1
            return self.operand(operands[0])
        raise NotImplementedError(f"Unsupported constant expr: {ce}")

    def _handlePhi(self, inst) -> List[Load]:
        bnum = type_size(self.llvmmodule, inst.type)
        phivar = Alloc(concrete_value(bnum, get_size_type()))
        ty = get_sb_type(self.llvmmodule, inst.type)
        L = Load(phivar, ty, [ty])
        self._addMapping(inst, L)
        self.phis.append((inst, phivar, L))
        return [L]

    def _parse_instruction(self, inst: ValueRef) -> List[Any]:
        opcode = inst.opcode
        if opcode == "alloca":
            return self._createAlloca(inst)
        elif opcode == "store":
            return self._createStore(inst)
        elif opcode == "load":
            return self._createLoad(inst)
        elif opcode == "ret":
            return self._createRet(inst)
        elif opcode == "icmp":
            return self._createCmp(inst)
        elif opcode == "fcmp":
            return self._createCmp(inst, isfloat=True)
        elif opcode == "fneg":
            return self._createFNeg(inst)
        elif opcode == "br":
            return self._createBranch(inst)
        elif opcode == "call":
            return self._createCall(inst)
        elif opcode == "unreachable":
            return self._createUnreachable(inst)
        elif opcode == "zext":
            return self._createExt(inst, False)
        elif opcode == "sext":
            return self._createExt(inst, True)
        elif opcode in ("uitofp", "sitofp", "fptosi", "fptoui", "fpext", "fptrunc"):
            return self._createReinterpCast(inst, opcode in ("uitofp", "fptoui"))
        elif opcode == "ptrtoint":
            return self._createPtrToInt(inst)
        elif opcode == "inttoptr":
            return self._createIntToPtr(inst)
        elif opcode == "trunc":
            return self._createTrunc(inst)
        elif opcode == "getelementptr":
            return self._createGep(inst)
        elif opcode == "bitcast":
            return self._createCast(inst)
        elif opcode in (
            "add",
            "sub",
            "sdiv",
            "mul",
            "udiv",
            "fadd",
            "fsub",
            "fdiv",
            "fmul",
        ):
            return self._createArith(inst, opcode)
        elif opcode in ["shl", "lshr", "ashr"]:
            return self._createShift(inst)
        elif opcode in ["and", "or", "xor"]:
            return self._createLogicOp(inst)
        elif opcode in ["srem", "urem"]:
            return self._createRem(inst)
        elif opcode == "select":
            return self._createSelect(inst)
        elif opcode == "phi":
            return self._handlePhi(inst)
        elif opcode == "switch":
            return self._handleSwitch(inst)
        else:
            raise NotImplementedError(f"Unsupported instruction: {inst}")

    def _parse_block(self, F: Function, block: ValueRef) -> None:
        """
        F     - slowbeast.Function
        block - llvm.block
        """
        B = self.bblock(block)
        assert B is not None, "Do not have a bblock"

        self.current_bblock = B

        for inst in block.instructions:
            # the result of parsing one llvm instruction
            # may be several slowbeast instructions
            try:
                instrs = self._parse_instruction(inst)
                assert (
                    inst.opcode
                    in ("bitcast", "call", "getelementptr", "ptrtoint", "inttoptr")
                    or instrs
                ), "No instruction was created"
                for I in instrs:
                    B.append(I)
            except Exception as e:
                print_stderr(f"Failed parsing llvm while parsing: {inst}", color="RED")
                raise e

        self.current_bblock = None
        assert B.fun() is F

    def _parse_fun(self, f: ValueRef) -> None:
        F = self.fun(f.name)
        self.current_fun = F

        # add mapping to arguments of the function
        for n, a in enumerate(f.arguments):
            self._addMapping(a, F.argument(n))

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
                var.insert_before(F.bblock(0).last())
                # place the writes to memory
                for i in range(0, inst.phi_incoming_count):
                    v, b = inst.phi_incoming(i)
                    B = self._bblocks[b]
                    S = Store(
                        self.operand(v), var, [load.type(), type_mgr().pointer_ty()]
                    )
                    S.insert_before(B.last())
            self.phis = []  # we handled these PHI nodes

        self.current_fun = None

    def _parse_initializer(
        self, G: GlobalVariable, g: ValueRef, ty: BytesType, ts: int
    ) -> None:
        c = get_constant(g.initializer)
        if c:
            # FIXME: add composed instruction
            G.set_init([Store(c, G, [ty, G.type()])])
            return
        # elif is_array_ty(g.initializer.type):
        #    parts=str(g.initializer.type).split()
        #    if parts[1] == 'x' and parts[2] == 'i8]':
        #    # FIXME: add String type to represent strings
        else:
            initsize = type_size(self.llvmmodule, g.initializer.type)
            if initsize and initsize == ts and "zeroinitializer" in str(g.initializer):
                # this global is whole zero-initialized
                G.set_zeroed()
                return
        print_stderr(
            f"Unsupported initializer: {g.initializer}",
            color="YELLOW",
        )

    def _parse_globals(self, m: ModuleRef) -> None:
        for g in m.global_variables:
            assert g.type.is_pointer
            # FIXME: check and set whether it is a constant
            ts = type_size(self.llvmmodule, g.type.element_type)
            ty = get_sb_type(self.llvmmodule, g.type.element_type)
            assert ts is not None, "Unsupported type size: {g.type.element_type}"
            G = GlobalVariable(
                concrete_value(ts, get_size_type_size()),
                g.name,
                const=g.is_global_constant(),
            )
            if g.initializer:
                self._parse_initializer(G, g, ty, ts)
            self.program.add_global(G)
            self._addMapping(g, G)

    def get_or_create_errno(self):
        # FIXME: errno is thread local
        errno_loc = self._errno_loc
        if errno_loc is not None:
            return errno_loc
        errn = GlobalVariable(concrete_value(4, get_size_type()), "errno")
        errno_loc = GlobalVariable(
            concrete_value(int(get_pointer_bitwidth() / 8), get_size_type()),
            "errno_loc",
        )
        self.program.add_global(errn)
        self.program.add_global(errno_loc)

        errno_loc.set_init([Store(errn, errno_loc, [errn.type(), errno_loc.type()])])
        self._errno_loc = errno_loc
        warn("errno not fully modelled, results may be invalid")

        return errno_loc

    def _parse_module(self, m: ModuleRef) -> None:
        self._parse_globals(m)

        # create the function at first,
        # because they may be operands of calls
        for f in m.functions:
            assert f.type.is_pointer, "Function pointer type is not a pointer"
            succ, retty = parse_fun_ret_ty(self.llvmmodule, f.type.element_type)
            if not succ:
                raise NotImplementedError(
                    f"Cannot parse function return type: {f.type.element_type} of fun: {f.name}"
                )
            args = [Argument(get_sb_type(self.llvmmodule, a.type)) for a in f.arguments]
            fun = Function(f.name, args, retty)
            self.program.add_fun(fun)
            self._funs[f] = fun

        for f in m.functions:
            if f.name in special_functions:
                # do not build these as we will replace their
                # calls with our stubs anyway
                continue

            self._parse_fun(f)

    def _parse(self, path: str) -> Program:
        m = _get_llvm_module(path)
        self.llvmmodule = m
        self._parse_module(m)

        # FIXME: set entry here?

        return self.program

    def parse(self, path: str) -> Program:
        return self._parse(path)


if __name__ == "__main__":
    from sys import argv

    parser = Parser()
    P: Program = parser.parse(argv[1])
    P.dump()
