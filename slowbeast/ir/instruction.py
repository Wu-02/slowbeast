#!/usr/bin/python

from . bblock import BBlock  # due to assertions
from . argument import Argument
from . program import ProgramElement

from .. util.debugging import print_highlight
from sys import stdout


class Instruction(ProgramElement):

    def __init__(self, ops=[]):
        super(Instruction, self).__init__()
        self._operands = ops
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

    def dump(self, ind=0, stream=stdout, color=True):
        super(Instruction, self).dump(ind, stream)
        if color:
            print_highlight(str(self), {"store": "WINE",
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
                            " " * ind, stream=stream)
        else:
            stream.write("{0}{1}\n".format(" " * ind, self))

    def getNextInstruction(self):
        assert self._bblock is not None
        assert self._bblock_idx is not None
        assert isinstance(self._bblock, BBlock)
        return self._bblock.getNextInstruction(self._bblock_idx)

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

    def __init__(self, ops=[]):
        super(ValueInstruction, self).__init__(ops)

    def isConstant(self):
        return False

    def asValue(self):
        return 'x{0}'.format(self.getID())


class Store(Instruction):
    def __init__(self, val, to):
        super(Store, self).__init__([val, to])
       # assert isinstance(val, Constant) or\
       #       isinstance(val, ValueInstruction) or\
       #       isinstance(val, Argument)
       # assert isinstance(to, ValueInstruction)

    def getPointerOperand(self):
        return self.getOperand(1)

    def getValueOperand(self):
        return self.getOperand(0)

    def __str__(self):
        return "store {0} to {1}".format(self.getValueOperand().asValue(),
                                         self.getPointerOperand().asValue())


class Load(ValueInstruction):
    """ Load 'bw' bytes from 'frm' """

    def __init__(self, frm, bw):
        super(Load, self).__init__([frm])
        self.bytes = bw

    def getBytesNum(self):
        return self.bytes

    def getPointerOperand(self):
        return self.getOperand(0)

    def __str__(self):
        return "x{0} = load {1}:{2}B".format(
            self.getID(), self.getPointerOperand().asValue(), self.bytes)


class Alloc(ValueInstruction):
    def __init__(self, size):
        super(Alloc, self).__init__()
        self._size = size

    def getSize(self):
        return self._size

    def __str__(self):
        return "x{0} = alloc {1} bytes".format(
            self.getID(), self.getSize().asValue())

    # the allocations return pointers, we need to compare them
    def __lt__(self, other):
        return (self.getID() < other.getID())

    def __le__(self, other):
        return(self.getID() <= other.getID())

    def __gt__(self, other):
        return(self.getID() > other.getID())

    def __ge__(self, other):
        return(self.getID() >= other.getID())

    # must override the hash since we defined the operators
    # defined in super class
    # def __hash__(self):
    #    return self.getID()


class Branch(Instruction):
    def __init__(self, cond, b1, b2):
        super(Branch, self).__init__([cond, b1, b2])
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
            self.getFalseSuccessor().asValue())


class Call(ValueInstruction):
    def __init__(self, wht, *operands):
        super(Call, self).__init__([*operands])
        self._function = wht

    def getCalledFunction(self):
        return self._function

    def getReturnValue(self):
        raise NotImplementedError("No return values in funs yet")
        # return self._function

    def __str__(self):
        r = "x{0} = call {1}(".format(self.getID(),
                                      self.getCalledFunction().asValue())
        r += ', '.join(map(lambda x: x.asValue(), self.getOperands()))
        return r + ')'


class Return(Instruction):
    def __init__(self, val=None):
        if val is None:
            super(Return, self).__init__([])
        else:
            super(Return, self).__init__([val])

    def __str__(self):
        if len(self.getOperands()) == 0:
            return "ret"
        return "ret {0}".format(str(self.getOperand(0).asValue()))


class Print(Instruction):
    def __init__(self, *operands):
        super(Print, self).__init__([*operands])

    def getCalledFunction(self):
        return self._function

    def __str__(self):
        r = 'print '
        for o in self._operands:
            r += o.asValue() + ' '
        return r


class Assert(Instruction):
    def __init__(self, cond, msg=None):
        super(Assert, self).__init__([cond, msg])

    def getMessage(self):
        ops = self.getOperands()
        assert len(ops) <= 2 and len(ops) >= 1
        if len(ops) == 1:
            return None
        return ops[1]

    def getCondition(self):
        return self.getOperand(0)

    def __str__(self):
        r = 'assert {0}'.format(self.getCondition().asValue())
        m = self.getMessage()
        if m:
            r += ", \"{0}\"".format(m)
        return r


class Assume(Instruction):
    def __init__(self, *operands):
        super(Assume, self).__init__([*operands])

    def __str__(self):
        r = 'assume '
        n = 0
        for o in self._operands:
            if n > 0:
                r += ' && '
            r += o.asValue()
            n += 1
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
            s = '<='
        elif p == Cmp.LT:
            s = '<'
        elif p == Cmp.GE:
            s = '>='
        elif p == Cmp.GT:
            s = '>'
        elif p == Cmp.EQ:
            s = '=='
        elif p == Cmp.NE:
            s = '!='
        else:
            raise NotImplementedError("Invalid comparison")

        if u:
            s += 'u'

        return s

    def __init__(self, p, val1, val2, unsgn=False):
        super(Cmp, self).__init__([val1, val2])
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
            Cmp.predicateStr(
                self.getPredicate(),
                self.isUnsigned()),
            self.getOperand(1).asValue())


class UnaryOperation(ValueInstruction):
    NEG = 1
    ZEXT = 2
    SEXT = 3
    EXTRACT = 4

    def __check(op):
        assert op >= UnaryOperation.NEG and op <= UnaryOperation.EXTRACT

    def __init__(self, op, a):
        super(UnaryOperation, self).__init__([a])
        UnaryOperation.__check(op)
        self._op = op

    def getOperation(self):
        return self._op


class Extend(UnaryOperation):
    def __init__(self, op, a, bw):
        assert bw.isConstant(), "Invalid bitwidth to extend"
        super(Extend, self).__init__(op, a)
        self._bw = bw

    def getBitWidth(self):
        return self._bw


class ZExt(Extend):
    def __init__(self, a, bw):
        super(ZExt, self).__init__(UnaryOperation.ZEXT, a, bw)

    def __str__(self):
        return "x{0} = zext {1} to {2}b".format(self.getID(),
                                                self.getOperand(0).asValue(),
                                                self.getBitWidth())


class SExt(Extend):
    def __init__(self, a, bw):
        super(SExt, self).__init__(UnaryOperation.SEXT, a, bw)

    def __str__(self):
        return "x{0} = sext {1} to {2}b".format(self.getID(),
                                                self.getOperand(0).asValue(),
                                                self.getBitWidth())


class ExtractBits(UnaryOperation):
    def __init__(self, val, start, end):
        assert start.isConstant(), "Invalid bitwidth to extend"
        assert end.isConstant(), "Invalid bitwidth to extend"
        super(ExtractBits, self).__init__(UnaryOperation.EXTRACT, val)
        self._start = start
        self._end = end

    def getRange(self):
        return (self._start, self._end)

    def getStart(self):
        return self._start

    def getEnd(self):
        return self._end

    def __str__(self):
        return "x{0} = extractbits {1}-{2} from {3}b".format(
            self.getID(), self.getStart(), self.getEnd(), self.getOperand(0).asValue())


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
        assert op >= BinaryOperation.ADD and op <= BinaryOperation.LAST

    def __init__(self, op, a, b):
        super(BinaryOperation, self).__init__([a, b])
        BinaryOperation.__check(op)
        self._op = op

    def getOperation(self):
        return self._op


class Add(BinaryOperation):
    def __init__(self, a, b):
        super(Add, self).__init__(BinaryOperation.ADD, a, b)

    def __str__(self):
        return "x{0} = {1} + {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())


class Sub(BinaryOperation):
    def __init__(self, a, b):
        super(Sub, self).__init__(BinaryOperation.SUB, a, b)

    def __str__(self):
        return "x{0} = {1} - {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())


class Mul(BinaryOperation):
    def __init__(self, a, b):
        super(Mul, self).__init__(BinaryOperation.MUL, a, b)

    def __str__(self):
        return "x{0} = {1} * {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())


class Div(BinaryOperation):
    def __init__(self, a, b):
        super(Div, self).__init__(BinaryOperation.DIV, a, b)

    def __str__(self):
        return "x{0} = {1} / {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())

class Rem(BinaryOperation):
    def __init__(self, a, b, unsigned=False):
        super(Rem, self).__init__(BinaryOperation.REM, a, b)
        self._unsigned = unsigned

    def isUnsigned(self):
        return self._unsigned

    def __str__(self):
        return "x{0} = {1} %{3} {2}".format(self.getID(),
                                            self.getOperand(0).asValue(),
                                            self.getOperand(1).asValue(),
                                            "u" if self.isUnsigned() else "")

class Shl(BinaryOperation):
    def __init__(self, a, b):
        super(Shl, self).__init__(BinaryOperation.SHL, a, b)

    def __str__(self):
        return "x{0} = {1} << {2}".format(self.getID(),
                                          self.getOperand(0).asValue(),
                                          self.getOperand(1).asValue())


class LShr(BinaryOperation):
    def __init__(self, a, b):
        super(LShr, self).__init__(BinaryOperation.LSHR, a, b)

    def __str__(self):
        return "x{0} = {1} l>> {2}".format(self.getID(),
                                           self.getOperand(0).asValue(),
                                           self.getOperand(1).asValue())


class AShr(BinaryOperation):
    def __init__(self, a, b):
        super(AShr, self).__init__(BinaryOperation.ASHR, a, b)

    def __str__(self):
        return "x{0} = {1} >> {2}".format(self.getID(),
                                          self.getOperand(0).asValue(),
                                          self.getOperand(1).asValue())


class And(BinaryOperation):
    def __init__(self, a, b):
        super(And, self).__init__(BinaryOperation.AND, a, b)

    def __str__(self):
        return "x{0} = {1} & {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())


class Or(BinaryOperation):
    def __init__(self, a, b):
        super(Or, self).__init__(BinaryOperation.OR, a, b)

    def __str__(self):
        return "x{0} = {1} | {2}".format(self.getID(),
                                         self.getOperand(0).asValue(),
                                         self.getOperand(1).asValue())


class Xor(BinaryOperation):
    def __init__(self, a, b):
        super(Xor, self).__init__(BinaryOperation.XOR, a, b)

    def __str__(self):
        return "x{0} = xor {1}, {2}".format(self.getID(),
                                            self.getOperand(0).asValue(),
                                            self.getOperand(1).asValue())
