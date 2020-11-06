from sys import stdout

from .bblock import BBlock  # due to assertions
from .program import ProgramElement

from ..util.debugging import print_highlight


class GlobalVariable(ProgramElement):
    def __init__(self, size, name, const=False):
        super().__init__()
        self._size = size
        self._name = name
        # is the pointed memory constant?
        self._isconst = const
        # sequence of instructions used to initialize this global
        self._init = []

    def isGlobal(self):
        return True

    def getSize(self):
        return self._size

    def getName(self):
        return self._name

    def hasInit(self):
        return self._init is not None

    def getInit(self):
        return self._init

    def setInit(self, I):
        for i in I:
            self.addMetadata("init", str(i))
        self._init = I

    def asValue(self):
        return "g{0}".format(self.getID())

    def __str__(self):
        return "{0} = global {1} of size {2}".format(
            self.asValue(), self.getName(), self.getSize()
        )

    def dump(self, ind=0, stream=stdout, color=True):
        super().dump(ind, stream, color)
        stream.write("{0}{1}\n".format(" " * ind, self))


class Instruction(ProgramElement):
    def __init__(self, ops=None):
        super().__init__()
        self._operands = ops or []
        self._bblock = None
        self._bblock_idx = None

    def getOperand(self, idx):
        assert idx < len(self._operands)
        return self._operands[idx]

    def getOperands(self):
        return self._operands

    def getOperandsNum(self):
        return len(self._operands)

    def setBBlock(self, bb, idx):
        assert bb, "None bblock is invalid"
        assert idx >= 0, "Invalid bblock idx"
        self._bblock = bb
        self._bblock_idx = idx

    def getBBlock(self):
        return self._bblock

    def getFunction(self):
        assert self._bblock
        return self._bblock.getFunction()

    def getBBlockIdx(self):
        return self._bblock_idx

    def dump(self, ind=0, stream=stdout, color=True):
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
                    "bblock": "GREEN",
                },
                " " * ind,
                stream=stream,
            )
        else:
            stream.write("{0}{1}\n".format(" " * ind, self))

    ###
    # Helper methods
    def insertBefore(self, i):
        assert self.getBBlock() is None
        assert self.getBBlockIdx() is None
        assert i.getBBlock() is not None
        assert i.getBBlockIdx() is not None
        return i.getBBlock().insert(self, i.getBBlockIdx())

    def getNextInstruction(self):
        assert self.getBBlock() is not None
        assert self.getBBlockIdx() is not None
        assert isinstance(self.getBBlock(), BBlock)
        return self.getBBlock().getNextInstruction(self.getBBlockIdx())


# Defined in super class
# def __eq__(self, other):
#    return self.getID() == other.getID()

# def __ne__(self, other):
#    return not(self.__eq__(self, other))

# def __hash__(self):
#    return self.getID()


class ValueInstruction(Instruction):
    """
    Instruction that returns a value
    """

    def __init__(self, ops=None):
        super().__init__(ops or [])

    def is_concrete(self):
        return False

    def asValue(self):
        return "x{0}".format(self.getID())


class Store(Instruction):
    def __init__(self, val, to):
        super().__init__([val, to])

    # assert isinstance(val, Constant) or\
    #       isinstance(val, ValueInstruction) or\
    #       isinstance(val, Argument)
    # assert isinstance(to, ValueInstruction)

    def getPointerOperand(self):
        return self.getOperand(1)

    def getValueOperand(self):
        return self.getOperand(0)

    def __str__(self):
        return "store {0} to {1}".format(
            self.getValueOperand().asValue(), self.getPointerOperand().asValue()
        )


class Load(ValueInstruction):
    """ Load 'bw' bytes from 'frm' """

    def __init__(self, frm, bw):
        super().__init__([frm])
        self.bytes = bw

    def getBytesNum(self):
        return self.bytes

    def getPointerOperand(self):
        return self.getOperand(0)

    def __str__(self):
        return "x{0} = load {1}:{2}B".format(
            self.getID(), self.getPointerOperand().asValue(), self.bytes
        )


class Alloc(ValueInstruction):
    def __init__(self, size):
        super().__init__()
        self._size = size

    def getSize(self):
        return self._size

    def __str__(self):
        return "x{0} = alloc {1} bytes".format(self.getID(), self.getSize().asValue())

    # the allocations return pointers, we need to compare them
    def __lt__(self, other):
        return self.getID() < other.getID()

    def __le__(self, other):
        return self.getID() <= other.getID()

    def __gt__(self, other):
        return self.getID() > other.getID()

    def __ge__(self, other):
        return self.getID() >= other.getID()

    # must override the hash since we defined the operators
    # defined in super class
    # def __hash__(self):
    #    return self.getID()


class Branch(Instruction):
    def __init__(self, cond, b1, b2):
        super().__init__([cond, b1, b2])
        assert isinstance(b1, BBlock)
        assert isinstance(b2, BBlock)

    def getCondition(self):
        return self.getOperand(0)

    def getTrueSuccessor(self):
        return self.getOperand(1)

    def getFalseSuccessor(self):
        return self.getOperand(2)

    def __str__(self):
        return "branch {0} ? {1} : {2}".format(
            self.getCondition().asValue(),
            self.getTrueSuccessor().asValue(),
            self.getFalseSuccessor().asValue(),
        )


class Call(ValueInstruction):
    def __init__(self, wht, *operands):
        super().__init__([*operands])
        self._function = wht

    def getCalledFunction(self):
        return self._function

    def getReturnValue(self):
        raise NotImplementedError("No return values in funs yet")
        # return self._function

    def __str__(self):
        r = "x{0} = call {1}(".format(self.getID(), self.getCalledFunction().asValue())
        r += ", ".join(map(lambda x: x.asValue(), self.getOperands()))
        return r + ")"


class Return(Instruction):
    def __init__(self, val=None):
        if val is None:
            super().__init__([])
        else:
            super().__init__([val])

    def __str__(self):
        if len(self.getOperands()) == 0:
            return "ret"
        return "ret {0}".format(str(self.getOperand(0).asValue()))


class Print(Instruction):
    def __init__(self, *operands):
        super().__init__([*operands])

    def __str__(self):
        r = "print "
        for o in self._operands:
            r += o.asValue() + " "
        return r


class Assert(Instruction):
    def __init__(self, cond, msg=None):
        super().__init__([cond, msg])

    def getMessage(self):
        ops = self.getOperands()
        assert len(ops) <= 2 and len(ops) >= 1
        if len(ops) == 1:
            return None
        return ops[1]

    def getCondition(self):
        return self.getOperand(0)

    def __str__(self):
        r = "assert {0}".format(self.getCondition().asValue())
        m = self.getMessage()
        if m:
            r += ', "{0}"'.format(m)
        return r


class Assume(Instruction):
    def __init__(self, *operands):
        super().__init__([*operands])

    def __str__(self):
        r = "assume "
        for n, o in enumerate(self._operands):
            if n > 0:
                r += " && "
            r += o.asValue()
        return r


class Cmp(ValueInstruction):
    LE = 1
    LT = 2
    GE = 3
    GT = 4
    EQ = 5
    NE = 6

    def predicateStr(p, u=False):
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

    def predicateNeg(p):
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

    def __init__(self, p, val1, val2, unsgn=False):
        super().__init__([val1, val2])
        self._predicate = p
        self._unsigned = unsgn

    def setUnsigned(self):
        """ Set that this comparison is unsigned """
        self._unsigned = True

    def isUnsigned(self):
        return self._unsigned

    def getPredicate(self):
        return self._predicate

    def __str__(self):
        return "{0} = cmp {1} {2} {3}".format(
            self.asValue(),
            self.getOperand(0).asValue(),
            Cmp.predicateStr(self.getPredicate(), self.isUnsigned()),
            self.getOperand(1).asValue(),
        )


class UnaryOperation(ValueInstruction):
    NEG = 1
    ZEXT = 2
    SEXT = 3
    EXTRACT = 4

    def __check(op):
        assert UnaryOperation.NEG <= op <= UnaryOperation.EXTRACT

    def __init__(self, op, a):
        super().__init__([a])
        UnaryOperation.__check(op)
        self._op = op

    def getOperation(self):
        return self._op


class Extend(UnaryOperation):
    def __init__(self, op, a, bw):
        assert bw.is_concrete(), "Invalid bitwidth to extend"
        super().__init__(op, a)
        self._bw = bw

    def getBitWidth(self):
        return self._bw


class ZExt(Extend):
    def __init__(self, a, bw):
        super().__init__(UnaryOperation.ZEXT, a, bw)

    def __str__(self):
        return "x{0} = zext {1} to {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getBitWidth()
        )


class SExt(Extend):
    def __init__(self, a, bw):
        super().__init__(UnaryOperation.SEXT, a, bw)

    def __str__(self):
        return "x{0} = sext {1} to {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getBitWidth()
        )


class ExtractBits(UnaryOperation):
    def __init__(self, val, start, end):
        assert start.is_concrete(), "Invalid bitwidth to extend"
        assert end.is_concrete(), "Invalid bitwidth to extend"
        super().__init__(UnaryOperation.EXTRACT, val)
        self._start = start
        self._end = end

    def getRange(self):
        return (self._start, self._end)

    def getStart(self):
        return self._start

    def getEnd(self):
        return self._end

    def __str__(self):
        return "x{0} = extractbits {1}-{2} from {3}".format(
            self.getID(), self.getStart(), self.getEnd(), self.getOperand(0).asValue()
        )


class BinaryOperation(ValueInstruction):
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

    def __check(op):
        assert BinaryOperation.ADD <= op <= BinaryOperation.LAST

    def __init__(self, op, a, b):
        super().__init__([a, b])
        BinaryOperation.__check(op)
        self._op = op

    def getOperation(self):
        return self._op


class Add(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.ADD, a, b)

    def __str__(self):
        return "x{0} = {1} + {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class Sub(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.SUB, a, b)

    def __str__(self):
        return "x{0} = {1} - {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class Mul(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.MUL, a, b)

    def __str__(self):
        return "x{0} = {1} * {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class Div(BinaryOperation):
    def __init__(self, a, b, unsigned=False):
        super().__init__(BinaryOperation.DIV, a, b)
        self._unsigned = unsigned

    def isUnsigned(self):
        return self._unsigned

    def __str__(self):
        return "x{0} = {1} /{3} {2}".format(
            self.getID(),
            self.getOperand(0).asValue(),
            self.getOperand(1).asValue(),
            "u" if self.isUnsigned() else "",
        )


class Rem(BinaryOperation):
    def __init__(self, a, b, unsigned=False):
        super().__init__(BinaryOperation.REM, a, b)
        self._unsigned = unsigned

    def isUnsigned(self):
        return self._unsigned

    def __str__(self):
        return "x{0} = {1} %{3} {2}".format(
            self.getID(),
            self.getOperand(0).asValue(),
            self.getOperand(1).asValue(),
            "u" if self.isUnsigned() else "",
        )


class Shl(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.SHL, a, b)

    def __str__(self):
        return "x{0} = {1} << {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class LShr(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.LSHR, a, b)

    def __str__(self):
        return "x{0} = {1} l>> {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class AShr(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.ASHR, a, b)

    def __str__(self):
        return "x{0} = {1} >> {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class And(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.AND, a, b)

    def __str__(self):
        return "x{0} = {1} & {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class Or(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.OR, a, b)

    def __str__(self):
        return "x{0} = {1} | {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )


class Xor(BinaryOperation):
    def __init__(self, a, b):
        super().__init__(BinaryOperation.XOR, a, b)

    def __str__(self):
        return "x{0} = xor {1}, {2}".format(
            self.getID(), self.getOperand(0).asValue(), self.getOperand(1).asValue()
        )
