from sys import stdout

from slowbeast.util.debugging import print_highlight
from .bblock import BBlock  # due to assertions
from .programelement import ProgramElement
from .types import Type, IntType, BoolType, PointerType, get_offset_type
from slowbeast.ir.bblock import BBlock
from slowbeast.ir.types import PointerType, Type
from typing import TextIO, Union


class GlobalVariable(ProgramElement):
    def __init__(self, size, name, const: bool = False) -> None:
        super().__init__()
        self._size = size
        self._name = name
        # is the pointed memory constant?
        self._isconst = const
        # sequence of instructions used to initialize this global
        self._init = []
        self._zeroed = False

    def is_global(self) -> bool:
        return True

    def type(self) -> PointerType:
        return PointerType()

    def size(self):
        return self._size

    def name(self):
        return self._name

    def has_init(self) -> bool:
        """
        Is this variable initialized? It is initialized if it has some associated init sequence
        or is zeroed. Note that it does not mean it is initialized entirely.
        """
        return self._init is not None or self._zeroed

    def set_name(self, nm) -> None:
        self._name = nm

    def set_zeroed(self) -> None:
        self.add_metadata("init", "zeroed")
        self._zeroed = True

    def is_zeroed(self) -> bool:
        return self._zeroed

    def init(self):
        return self._init

    def set_init(self, I) -> None:
        for i in I:
            self.add_metadata("init", str(i))
        self._init = I

    def as_value(self) -> str:
        return f"g{self.get_id()}"

    def __str__(self) -> str:
        return f"{self.as_value()} = global {self.name()} of size {self.size()}"

    def dump(self, ind: int = 0, stream: TextIO = stdout, color: bool = True) -> None:
        super().dump(ind, stream, color)
        stream.write(f"{' ' * ind}{self}\n")


class Instruction(ProgramElement):
    def __init__(self, ops=None) -> None:
        super().__init__()
        self._operands = ops or []
        self._bblock = None
        self._bblock_idx = None

    def operand(self, idx):
        assert idx < len(self._operands)
        return self._operands[idx]

    def operands(self):
        return self._operands

    def operands_num(self) -> int:
        return len(self._operands)

    def set_bblock(self, bb, idx) -> None:
        assert bb, "None bblock is invalid"
        assert idx >= 0, "Invalid bblock idx"
        self._bblock = bb
        self._bblock_idx = idx

    def bblock(self):
        return self._bblock

    def fun(self):
        assert self._bblock
        return self._bblock.fun()

    def bblock_idx(self):
        return self._bblock_idx

    def dump(self, ind: int = 0, stream: TextIO = stdout, color: bool = True) -> None:
        super().dump(ind, stream)
        if color:
            print_highlight(
                str(self),
                {
                    "store": "WINE",
                    "load": "WINE",
                    "sext": "WINE",
                    "zext": "WINE",
                    "call": "WINE",
                    "assert": "WINE",
                    "assume": "WINE",
                    "branch": "WINE",
                    "ret": "WINE",
                    "cmp": "WINE",
                    "alloc": "WINE",
                    "cast": "WINE",
                    "bblock": "GREEN",
                },
                " " * ind,
                stream=stream,
            )
        else:
            stream.write(f"{' ' * ind}{self}\n")

    ###
    # Helper methods
    def insert_before(self, i):
        assert self.bblock() is None
        assert self.bblock_idx() is None
        assert i.bblock() is not None
        assert i.bblock_idx() is not None
        return i.bblock().insert(self, i.bblock_idx())

    def get_next_inst(self):
        assert self.bblock() is not None
        assert self.bblock_idx() is not None
        assert isinstance(self.bblock(), BBlock)
        return self.bblock().get_next_inst(self.bblock_idx())


class ValueInstruction(Instruction):
    """
    Instruction that generates a value
    """

    def __init__(self, ops=None) -> None:
        super().__init__(ops or [])
        self._name = None

    def is_concrete(self) -> bool:
        return False

    def set_name(self, nm) -> None:
        self._name = nm

    def as_value(self) -> str:
        if self._name:
            return f"{self._name}"
        return f"x{self.get_id()}"


class ValueTypedInstruction(ValueInstruction):
    """
    ValueInstruction with associated type of the generated value
    """

    def __init__(self, ty, ops=None) -> None:
        super().__init__(ops or [])
        self._type = ty

    def type(self):
        return self._type


class Store(Instruction):
    """Store 'val' which has 'bw' bytes to 'to'"""

    # NOTE: having 'bw' is important for lazy allocation of objects
    # since when we create SMT bitvector objects, we must specify
    # their bitwidth (well, we could do that dynamically, but for most
    # situations this is much easier...)
    def __init__(self, val, to, bw) -> None:
        assert val, val
        assert to, to
        super().__init__([val, to])
        self._bw = bw

    def pointer_operand(self):
        return self.operand(1)

    def value_operand(self):
        return self.operand(0)

    def bytewidth(self):
        return self._bw

    def bitwidth(self) -> int:
        return self._bw * 8

    def __str__(self) -> str:
        return "store {1} to {2}:{0}B".format(
            self._bw,
            self.value_operand().as_value(),
            self.pointer_operand().as_value(),
        )


class Load(ValueTypedInstruction):
    """Load value of type 'ty' from 'frm'"""

    def __init__(self, frm: Union[GlobalVariable, Instruction], ty: Type) -> None:
        assert isinstance(ty, Type), ty
        assert isinstance(frm, (Instruction, GlobalVariable)), frm
        super().__init__(ty, [frm])

    def bytewidth(self):
        return self._type.bytewidth()

    def bitwidth(self):
        return self._type.bitwidth()

    def pointer_operand(self):
        return self.operand(0)

    def __str__(self) -> str:
        return "x{0} = load {1}:{2}".format(
            self.get_id(), self.pointer_operand().as_value(), self.type()
        )


class Alloc(ValueInstruction):
    def __init__(self, size, on_heap: bool = False) -> None:
        assert isinstance(on_heap, bool), on_heap
        super().__init__()
        self._size = size
        self._is_heap = on_heap

    def size(self):
        return self._size

    def type(self) -> PointerType:
        return PointerType()

    def __str__(self) -> str:
        return "{0} = alloc {1} bytes{2}".format(
            self.as_value(),
            self.size().as_value(),
            " on heap" if self._is_heap else "",
        )

    # the allocations return pointers, we need to compare them
    def __lt__(self, other):
        return self.get_id() < other.get_id()

    def __le__(self, other):
        return self.get_id() <= other.get_id()

    def __gt__(self, other):
        return self.get_id() > other.get_id()

    def __ge__(self, other):
        return self.get_id() >= other.get_id()

    # must override the hash since we defined the operators
    # defined in super class
    # def __hash__(self):
    #    return self.get_id()


class Branch(Instruction):
    def __init__(self, cond, b1: BBlock, b2: BBlock) -> None:
        super().__init__([cond, b1, b2])
        assert isinstance(b1, BBlock)
        assert isinstance(b2, BBlock)

    def condition(self):
        return self.operand(0)

    def true_successor(self):
        return self.operand(1)

    def false_successor(self):
        return self.operand(2)

    def __str__(self) -> str:
        return "branch {0} ? {1} : {2}".format(
            self.condition().as_value(),
            self.true_successor().as_value(),
            self.false_successor().as_value(),
        )


class Switch(Instruction):
    def __init__(self, val, default: BBlock, cases: list) -> None:
        super().__init__([val, default] + cases)
        assert isinstance(default, BBlock), default
        assert isinstance(cases, list), cases
        assert all(map(lambda p: p[0].type().is_int(), cases)), cases
        assert all(map(lambda p: isinstance(p[1], BBlock), cases)), cases

    def condition(self):
        return self.operand(0)

    def default_bblock(self):
        return self.operand(1)

    def cases(self):
        return self.operands()[2:]

    def __str__(self) -> str:
        return (
            "switch on {0}:\n  {1}".format(
                self.condition().as_value(),
                "\n  ".join(
                    f"{v.as_value() : >7} -> {c.as_value()}" for (v, c) in self.cases()
                ),
            )
            + f"\n  default -> {self.default_bblock().as_value()}"
        )


class Call(ValueTypedInstruction):
    def __init__(self, wht, ty, *operands) -> None:
        super().__init__(ty, [*operands])
        self._function = wht

    def called_function(self):
        return self._function

    def type(self):
        return self._function.type()

    def return_value(self):
        raise NotImplementedError("No return values in funs yet")
        # return self._function

    def __str__(self) -> str:
        r = f"x{self.get_id()} = call {self.called_function().as_value()}("
        r += ", ".join(map(lambda x: x.as_value(), self.operands()))
        return r + f") -> {self._type}"


class Return(Instruction):
    def __init__(self, val=None) -> None:
        if val is None:
            super().__init__([])
        else:
            super().__init__([val])

    def __str__(self) -> str:
        if len(self.operands()) == 0:
            return "ret"
        return f"ret {str(self.operand(0).as_value())}"


class Thread(Call):
    def __init__(self, wht, *operands) -> None:
        super().__init__(wht, get_offset_type(), *operands)

    def called_function(self):
        return self._function

    def type(self):
        return self._function.type()

    def return_value(self):
        raise NotImplementedError("No return values in funs yet")
        # return self._function

    def __str__(self) -> str:
        r = f"x{self.get_id()} = thread {self.called_function().as_value()}("
        r += ", ".join(map(lambda x: x.as_value(), self.operands()))
        return r + f") -> {self._type}"


class ThreadExit(Return):
    def __init__(self, val=None) -> None:
        super().__init__(val)

    def __str__(self) -> str:
        if len(self.operands()) == 0:
            return "thread exit"
        return f"thread exit ret {self.operand(0).as_value()}"


class ThreadJoin(ValueTypedInstruction):
    def __init__(self, ty, ops=None) -> None:
        super().__init__(ty, ops)

    def __str__(self) -> str:
        if len(self.operands()) == 0:
            r = "thread join"
        else:
            r = f"x{self.get_id()} = thread join ("
        r += ", ".join(map(lambda x: x.as_value(), self.operands()))
        return r + ")"


class Print(Instruction):
    def __init__(self, *operands) -> None:
        super().__init__([*operands])

    def __str__(self) -> str:
        r = "print "
        for o in self._operands:
            r += o.as_value() + " "
        return r


class Assert(Instruction):
    def __init__(self, cond, msg=None) -> None:
        super().__init__([cond, msg])

    def msg(self):
        ops = self.operands()
        assert len(ops) <= 2 and len(ops) >= 1
        if len(ops) == 1:
            return None
        return ops[1]

    def condition(self):
        return self.operand(0)

    def __str__(self) -> str:
        r = f"assert {self.condition().as_value()}"
        m = self.msg()
        if m:
            r += f', "{m}"'
        return r


class Assume(Instruction):
    def __init__(self, *operands) -> None:
        super().__init__([*operands])

    def __str__(self) -> str:
        r = "assume "
        for n, o in enumerate(self._operands):
            if n > 0:
                r += " && "
            r += o.as_value()
        return r


class Cmp(ValueTypedInstruction):
    LE = 1
    LT = 2
    GE = 3
    GT = 4
    EQ = 5
    NE = 6

    def predicate_str(p, u: bool = False) -> str:
        if p == Cmp.LE:
            s = "<="
        elif p == Cmp.LT:
            s = "<"
        elif p == Cmp.GE:
            s = ">="
        elif p == Cmp.GT:
            s = ">"
        elif p == Cmp.EQ:
            s = "=="
        elif p == Cmp.NE:
            s = "!="
        else:
            raise NotImplementedError("Invalid comparison")

        if u:
            s += "u"

        return s

    def predicate_neg(p) -> int:
        if p == Cmp.LE:
            return Cmp.GT
        if p == Cmp.LT:
            return Cmp.GE
        if p == Cmp.GE:
            return Cmp.LT
        if p == Cmp.GT:
            return Cmp.LE
        if p == Cmp.EQ:
            return Cmp.NE
        if p == Cmp.NE:
            return Cmp.EQ

        raise NotImplementedError("Invalid comparison")

    def __init__(self, p, val1, val2, unsgn: bool = False, fp: bool = False) -> None:
        super().__init__(BoolType(), [val1, val2])
        self._predicate = p
        self._unsigned = unsgn
        self._fp = fp

    def set_float(self) -> None:
        """Set that this comparison is on floating-point numbers"""
        self._fp = True

    def is_float(self) -> bool:
        return self._fp

    def set_unsigned(self) -> None:
        """Set that this comparison is unsigned"""
        self._unsigned = True

    def is_unsigned(self) -> bool:
        return self._unsigned

    def predicate(self):
        return self._predicate

    def __str__(self) -> str:
        return "{0} = {4}cmp {1} {2} {3}".format(
            self.as_value(),
            self.operand(0).as_value(),
            Cmp.predicate_str(self.predicate(), self.is_unsigned()),
            self.operand(1).as_value(),
            "f" if self._fp else "",
        )


class UnaryOperation(ValueTypedInstruction):
    NEG = 1
    ZEXT = 2
    SEXT = 3
    EXTRACT = 4
    CAST = 5  # reinterpret cast
    ABS = 6
    FP_OP = 7  # floating-point operation
    LAST_UNARY_OP = 7

    # TODO make SEXT and ZEXT also reinterpret cast?

    def __check(op):
        assert UnaryOperation.NEG <= op <= UnaryOperation.LAST_UNARY_OP

    def __init__(self, op: "UnaryOperation", a, ty=None) -> None:
        """Some unary operations do not inherit the type -- set it in 'ty'"""
        super().__init__(ty or a.type(), [a])
        UnaryOperation.__check(op)
        self._op = op

    def operation(self) -> "UnaryOperation":
        return self._op


class Abs(UnaryOperation):
    """Absolute value"""

    def __init__(self, val) -> None:
        super().__init__(UnaryOperation.ABS, val)

    def __str__(self) -> str:
        return f"x{self.get_id()} = abs({self.operand(0).as_value()})"


class Extend(UnaryOperation):
    def __init__(self, op: UnaryOperation, a, bw) -> None:
        assert bw.is_concrete(), "Invalid bitwidth to extend"
        super().__init__(op, a, ty=IntType(bw.value()))
        self._bw = bw

    def bitwidth(self):
        return self._bw


class ZExt(Extend):
    def __init__(self, a, bw) -> None:
        super().__init__(UnaryOperation.ZEXT, a, bw)

    def __str__(self) -> str:
        return "x{0} = zext {1} to {2}".format(
            self.get_id(), self.operand(0).as_value(), self.bitwidth()
        )


class SExt(Extend):
    def __init__(self, a, bw) -> None:
        super().__init__(UnaryOperation.SEXT, a, bw)

    def __str__(self) -> str:
        return "x{0} = sext {1} to {2}".format(
            self.get_id(), self.operand(0).as_value(), self.bitwidth()
        )


class Cast(UnaryOperation):
    def __init__(self, a, ty: Type, sgn: bool = True) -> None:
        assert isinstance(ty, Type)
        super().__init__(UnaryOperation.CAST, a, ty=ty)
        self._signed = sgn

    def casttype(self):
        return self.type()

    def signed(self) -> bool:
        return self._signed

    def __str__(self) -> str:
        return "x{0} = cast {1} to {2}{3}".format(
            self.get_id(),
            self.operand(0).as_value(),
            "signed " if self._signed else "",
            self.casttype(),
        )


class Neg(UnaryOperation):
    """Negate the number (return the same number with opposite sign)"""

    def __init__(self, val, fp) -> None:
        super().__init__(UnaryOperation.NEG, val)
        self._fp = fp

    def is_fp(self):
        return self._fp

    def __str__(self) -> str:
        return "x{0} = -({1}){2}".format(
            self.get_id(), self.operand(0).as_value(), "f" if self._fp else ""
        )


class ExtractBits(UnaryOperation):
    def __init__(self, val, start, end) -> None:
        assert start.is_concrete(), "Invalid bitwidth to extend"
        assert end.is_concrete(), "Invalid bitwidth to extend"
        super().__init__(
            UnaryOperation.EXTRACT, val, ty=IntType(end.value() - start.value() + 1)
        )
        self._start = start
        self._end = end

    def range(self):
        return (self._start, self._end)

    def start(self):
        return self._start

    def end(self):
        return self._end

    def __str__(self) -> str:
        return "x{0} = extractbits {1}-{2} from {3}".format(
            self.get_id(), self.start(), self.end(), self.operand(0).as_value()
        )


class FpOp(UnaryOperation):
    """Floating-point special operations"""

    IS_INF = 1
    IS_NAN = 2
    FPCLASSIFY = 3
    SIGNBIT = 4

    def op_to_str(op) -> str:
        if op == FpOp.IS_INF:
            return "isinf"
        if op == FpOp.IS_NAN:
            return "isnan"
        if op == FpOp.FPCLASSIFY:
            return "fpclassify"
        if op == FpOp.SIGNBIT:
            return "signbit"
        return "uknwn"

    def __init__(self, fp_op, val) -> None:
        assert FpOp.IS_INF <= fp_op <= FpOp.SIGNBIT
        super().__init__(UnaryOperation.FP_OP, val)
        self._fp_op = fp_op

    def fp_operation(self):
        return self._fp_op

    def __str__(self) -> str:
        return "x{0} = fp {1} {2}".format(
            self.get_id(), FpOp.op_to_str(self._fp_op), self.operand(0).as_value()
        )


class BinaryOperation(ValueTypedInstruction):
    # arith
    ADD = 1
    SUB = 2
    MUL = 3
    DIV = 4
    REM = 11
    # bitwise
    SHL = 5
    LSHR = 6
    ASHR = 7
    # logical
    AND = 8
    OR = 9
    XOR = 10
    # more logicals to come ...
    LAST = 12

    def __init__(self, op, a, b) -> None:
        isptr = a.type().is_pointer() or b.type().is_pointer()
        assert isptr or a.type() == b.type(), f"{a} ({a.type()}), {b} ({b.type()})"
        assert BinaryOperation.ADD <= op <= BinaryOperation.LAST
        super().__init__(PointerType() if isptr else a.type(), [a, b])
        self._op = op

    def operation(self):
        return self._op


class Add(BinaryOperation):
    def __init__(self, a, b, fp: bool = False) -> None:
        super().__init__(BinaryOperation.ADD, a, b)
        self._fp = fp

    def is_fp(self) -> bool:
        return self._fp

    def __str__(self) -> str:
        return "x{0} = {1} +{3} {2}".format(
            self.get_id(),
            self.operand(0).as_value(),
            self.operand(1).as_value(),
            "." if self._fp else "",
        )


class Sub(BinaryOperation):
    def __init__(self, a, b, fp: bool = False) -> None:
        super().__init__(BinaryOperation.SUB, a, b)
        self._fp = fp

    def is_fp(self) -> bool:
        return self._fp

    def __str__(self) -> str:
        return "x{0} = {1} -{3} {2}".format(
            self.get_id(),
            self.operand(0).as_value(),
            self.operand(1).as_value(),
            "." if self._fp else "",
        )


class Mul(BinaryOperation):
    def __init__(self, a, b, fp: bool = False) -> None:
        super().__init__(BinaryOperation.MUL, a, b)
        self._fp = fp

    def is_fp(self) -> bool:
        return self._fp

    def __str__(self) -> str:
        return "x{0} = {1} *{3} {2}".format(
            self.get_id(),
            self.operand(0).as_value(),
            self.operand(1).as_value(),
            "." if self._fp else "",
        )


class Div(BinaryOperation):
    def __init__(self, a, b, unsigned: bool = False, fp: bool = False) -> None:
        super().__init__(BinaryOperation.DIV, a, b)
        self._unsigned = unsigned
        self._fp = fp

    def is_fp(self) -> bool:
        return self._fp

    def is_unsigned(self) -> bool:
        return self._unsigned

    def __str__(self) -> str:
        return "x{0} = {1} /{3}{4} {2}".format(
            self.get_id(),
            self.operand(0).as_value(),
            self.operand(1).as_value(),
            "u" if self.is_unsigned() else "",
            "." if self._fp else "",
        )


class Rem(BinaryOperation):
    def __init__(self, a, b, unsigned: bool = False) -> None:
        super().__init__(BinaryOperation.REM, a, b)
        self._unsigned = unsigned

    def is_unsigned(self) -> bool:
        return self._unsigned

    def __str__(self) -> str:
        return "x{0} = {1} %{3} {2}".format(
            self.get_id(),
            self.operand(0).as_value(),
            self.operand(1).as_value(),
            "u" if self.is_unsigned() else "",
        )


class Shl(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.SHL, a, b)

    def __str__(self) -> str:
        return "x{0} = {1} << {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


class LShr(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.LSHR, a, b)

    def __str__(self) -> str:
        return "x{0} = {1} l>> {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


class AShr(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.ASHR, a, b)

    def __str__(self) -> str:
        return "x{0} = {1} >> {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


class And(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.AND, a, b)

    def __str__(self) -> str:
        return "x{0} = {1} & {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


class Or(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.OR, a, b)

    def __str__(self) -> str:
        return "x{0} = {1} | {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


class Xor(BinaryOperation):
    def __init__(self, a, b) -> None:
        super().__init__(BinaryOperation.XOR, a, b)

    def __str__(self) -> str:
        return "x{0} = xor {1}, {2}".format(
            self.get_id(), self.operand(0).as_value(), self.operand(1).as_value()
        )


# TODO: do we want this instruction? (can we replace it somehow without
# creating an artificial braching?).
class Ite(ValueTypedInstruction):
    """if-then-else: assign a value based on a condition"""

    def __init__(self, cond, op1, op2) -> None:
        assert cond.type().bitwidth() == 1
        assert op1.type() == op2.type(), "Invalid types in Ite"
        super().__init__(op1.type(), [op1, op2])
        self._cond = cond

    def condition(self):
        return self._cond

    def __repr__(self) -> str:
        return (
            f"{self.as_value()} = if {self._cond.as_value()} then "
            f"{self.operand(0).as_value()} else {self.operand(1).as_value()}"
        )
