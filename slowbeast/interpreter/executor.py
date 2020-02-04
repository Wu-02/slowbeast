import sys
from .. util.debugging import dbg
from .. ir.instruction import *
from .. ir.value import *
from . errors import ExecutionError


class Executor:
    """
    Class that takes care of executing single instructions
    """

    def __init__(self):
        pass

    def execStore(self, state, instr):
        assert isinstance(instr, Store)
        value = state.eval(instr.getValueOperand())
        to = state.eval(instr.getPointerOperand())
        assert isinstance(value, Value)
        assert to.isPointer()

        states = state.write(to, value)
        for s in states:
            if s.isReady():
                s.pc = s.pc.getNextInstruction()
        return states

    def execLoad(self, state, instr):
        assert isinstance(instr, Load)
        frm = state.eval(instr.getPointerOperand())
        assert frm.isPointer()
        states = state.read(frm, dest=instr, bytesNum=instr.getBytesNum())
        for s in states:
            if s.isReady():
                s.pc = s.pc.getNextInstruction()
        return states

    def execAlloc(self, state, instr):
        assert isinstance(instr, Alloc)
        size = state.eval(instr.getSize())
        ptr = state.memory.allocate(size, instr)
        state.set(instr, ptr)
        state.pc = state.pc.getNextInstruction()

        return [state]

    def execCmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        if op1.isPointer():
            if not op2.isPointer():
                raise ExecutionError("Comparison of pointer to a constant")
            if op1.object.getID() != op2.object.getID():
                raise ExecutionError("Comparison of unrelated pointers")
            op1 = op1.offset
            op2 = op2.offset
        else:
            op1 = op1.getValue()
            op2 = op2.getValue()
        x = None
        p = instr.getPredicate()
        if p == Cmp.LE:
            x = op1 <= op2
        elif p == Cmp.LT:
            x = op1 < op2
        elif p == Cmp.GE:
            x = op1 >= op2
        elif p == Cmp.GT:
            x = op1 > op2
        elif p == Cmp.EQ:
            x = op1 == op2
        elif p == Cmp.NE:
            x = op1 != op2

        state.set(instr, Constant(x, 1))
        state.pc = state.pc.getNextInstruction()

        return [state]

    def execPrint(self, state, instr):
        assert isinstance(instr, Print)
        for x in instr.getOperands():
            v = state.eval(x)
            if isinstance(v, Constant):
                v = v.getValue()
            sys.stdout.write(str(v))
        sys.stdout.write('\n')
        sys.stdout.flush()

        state.pc = state.pc.getNextInstruction()

        return [state]

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        c = instr.getCondition()
        assert isinstance(c, ValueInstruction) or c.isConstant()
        cv = state.eval(instr.getCondition()).getValue()

        if cv:
            succ = instr.getTrueSuccessor()
        elif cv == False:
            succ = instr.getFalseSuccessor()
        else:
            raise ExecutionError("Indeterminite condition")

        assert succ
        if not succ.empty():
            state.pc = succ.getInstruction(0)
        else:
            state.pc = None

        return [state]

    def execAssert(self, state, instr):
        assert isinstance(instr, Assert)
        for o in instr.getOperands():
            v = state.eval(o)
            assert isinstance(v, Constant)
            if v.getValue() != True:
                state.setError(
                    ExecutionError(
                        "Assertion failed: {0} is {1} (!= True)".format(
                            o, v)))
                return [state]

        state.pc = state.pc.getNextInstruction()
        return [state]

    def execAssume(self, state, instr):
        assert isinstance(instr, Assume)
        state.pc = state.pc.getNextInstruction()
        for o in instr.getOperands():
            v = state.eval(o)
            assert v.isConstant()
            assert v.isBool()
            if v.getValue() != True:
                print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                state.dump()
                break

        return [state]

    def execUnaryOp(self, state, instr):
        raise NotImplementedError(
            "Concrete executor does not implement unary op yet")

    def execBinaryOp(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1c = state.eval(instr.getOperand(0))
        op2c = state.eval(instr.getOperand(1))
        op1 = None
        op2 = None
        bw = max(op1c.getByteWidth(), op2c.getByteWidth())
        # if one of the operands is a pointer,
        # lift the other to pointer too
        if op1c.isPointer():
            if not op2c.isPointer():
                assert isinstance(op2c, Constant)
                # adding a constant -- create a pointer
                # to the object with the right offset
                op2c = Pointer(op1c.object, op2c.getValue())
        elif op2c.isPointer():
            if not op1c.isPointer():
                assert isinstance(op1c, Constant)
                # adding a constant -- create a pointer
                # to the object with the right offset
                op1c = Pointer(op2c.object, op1c.getValue())
        else:
            op1 = op1c.getValue()
            op2 = op2c.getValue()

        if op1c.isPointer() and op1c.object != op2c.object:
            raise ExecutionError("Pointer arithmetic on unrelated pointers")

        r = None
        if instr.getOperation() == BinaryOperation.ADD:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset + op2c.offset)
            else:
                r = Constant(op1 + op2, bw)
        elif instr.getOperation() == BinaryOperation.SUB:
            if isinstance(op1c, Pointer):
                assert isinstance(op2c, Pointer)
                r = Pointer(op1c.object, op1c.offset - op2c.offset)
            else:
                r = Constant(op1 - op2)
        elif instr.getOperation() == BinaryOperation.MUL:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset * op2c.offset)
            else:
                r = Constant(op1 * op2)
        elif instr.getOperation() == BinaryOperation.DIV:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset / op2c.offset)
            else:
                r = Constant(op1 / op2)
        else:
            raise NotImplementedError("Binary operation: " + str(instr))

        state.set(instr, r)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        dbg("-- CALL {0} --".format(fun.getName()))
        if fun.isUndefined():
            state.setError(
                ExecutionError(
                    "Called undefined function: {0}".format(
                        fun.getName())))
            return [state]
        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x: state.eval(y) for (x, y)
                   in zip(fun.getArguments(), instr.getOperands())}
        state.pushCall(instr, fun, mapping)
        return [state]

    def execRet(self, state, instr):
        assert isinstance(instr, Return)

        # obtain the return value (if any)
        ret = None
        if len(instr.getOperands()) != 0:  # returns something
            ret = state.eval(instr.getOperand(0))

        # pop the call frame and get the return site
        rs = state.popCall()
        if rs is None:  # popped the last frame
            if ret.isPointer():
                state.setError(
                    ExecutionError("Returning a pointer from main function"))
                return [state]
            assert ret.isConstant()
            state.setExited(ret.getValue())
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.getNextInstruction()
        return [state]

    def execute(self, state, instr):
        """
        Execute the next instruction in the state and modify the state accordingly.
        If the instruction terminated the program, return the exit code.
        TODO: exceptional termination (like assert?)
        """
        # debug print
        dbg("({2}) {0}: {1}".format(
            instr.getFunction().getName(), str(instr), state.getID()))

        # TODO: add an opcode to instruction and check only the opcode
        states = None
        if isinstance(instr, Store):
            states = self.execStore(state, instr)
        elif isinstance(instr, Load):
            states = self.execLoad(state, instr)
        elif isinstance(instr, Alloc):
            states = self.execAlloc(state, instr)
        elif isinstance(instr, Cmp):
            states = self.execCmp(state, instr)
        elif isinstance(instr, Print):
            states = self.execPrint(state, instr)
        elif isinstance(instr, Branch):
            states = self.execBranch(state, instr)
        elif isinstance(instr, Assert):
            states = self.execAssert(state, instr)
        elif isinstance(instr, Assume):
            states = self.execAssume(state, instr)
        elif isinstance(instr, UnaryOperation):
            states = self.execUnaryOp(state, instr)
        elif isinstance(instr, BinaryOperation):
            states = self.execBinaryOp(state, instr)
        elif isinstance(instr, Call):
            states = self.execCall(state, instr)
        elif isinstance(instr, Return):
            states = self.execRet(state, instr)
        else:
            raise NotImplementedError(str(instr))

        return states
