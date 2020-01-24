import sys
from .. ir.instruction import *
from .. ir.value import *
from . errors import ExecutionError

class Executor:
    """
    Class that takes care of executing single instructions
    """
    def __init__(self, dbg=False):
        self._debug = dbg

    def execStore(self, state, instr):
        assert isinstance(instr, Store)
        value = state.eval(instr.getValueOperand())
        to = state.eval(instr.getPointerOperand())
        assert to.isPointer()
        to.object.write(value, to.offset)
        state.pc = state.pc.getNextInstruction()

    def execLoad(self, state, instr):
        assert isinstance(instr, Load)
        frm = state.eval(instr.getPointerOperand())
        assert frm.isPointer()
        state.set(instr, frm.object.read(instr.getBytesNum(), frm.offset))
        state.pc = state.pc.getNextInstruction()

    def execAlloc(self, state, instr):
        assert isinstance(instr, Alloc)
        o = state.memory.allocate(instr.getSize().value)
        o.object.setAllocation(instr)
        state.set(instr, o)
        state.pc = state.pc.getNextInstruction()

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
            op1 = op1.value
            op2 = op2.value
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

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        c = instr.getCondition()
        assert isinstance(c, ValueInstruction) or c.isConstant()
        cv = state.eval(instr.getCondition()).value

        if cv == True:
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

    def execAssert(self, state, instr):
        assert isinstance(instr, Assert)
        for o in instr.getOperands():
            v = state.eval(o)
            assert isinstance(v, Constant)
            if v.getValue() != True:
                raise ExecutionError("Assertion failed: {0} is {1} (!= True)".format(o, v))
        state.pc = state.pc.getNextInstruction()

    def execAssume(self, state, instr):
        assert isinstance(instr, Assume)
        # assume is the same as assert during interpretation, but to make it different,
        # just make it dump the state and continue the execution
        for o in instr.getOperands():
            v = state.eval(o)
            assert isinstance(v, Constant)
            if v.getValue() != True:
                print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                break
        state.pc = state.pc.getNextInstruction()

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
                op2c = Pointer(op1c.object, op2c.value)
        elif op2c.isPointer():
            if not op1c.isPointer():
                assert isinstance(op1c, Constant)
                # adding a constant -- create a pointer
                # to the object with the right offset
                op1c = Pointer(op2c.object, op1c.value)
        else:
            op1 = op1c.value
            op2 = op2c.value

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

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        if self._debug:
            sys.stderr.write("[sb dbg]: -- CALL {0} --\n".format(fun.getName()))
        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x : state.eval(y) for (x, y)\
                   in zip(fun.getArguments(), instr.getOperands())}
        state.pc = state.call(instr, fun, mapping)

    def execRet(self, state, instr):
        if self._debug:
            sys.stderr.write("[sb dbg]: -- RET --\n")
        assert isinstance(instr, Return)
        if len(instr.getOperands()) == 0: # returns nothing
            rs = state.ret()
        else:
            ret = state.eval(instr.getOperand(0))
            rs = state.ret()
            if rs is None: # popped the last frame
                if ret.isPointer():
                    raise ExecutionError("Returning a pointer from main function")
                assert isinstance(ret, Constant)
                state.pc = None
                return ret.getValue()
            state.set(rs, ret)

        state.pc = rs.getNextInstruction()
        return None

    def execute(self, state, instr):
        """
        Execute the next instruction in the state and modify the state accordingly.
        If the instruction terminated the program, return the exit code.
        TODO: exceptional termination (like assert?)
        """
        # debug print
        if self._debug:
            sys.stderr.write("[sb dbg]: {0}\n".format(instr))

        # TODO: add an opcode to instruction and check only the opcode
        ec = None
        if isinstance(instr, Store):
            self.execStore(state, instr)
        elif isinstance(instr, Load):
            self.execLoad(state, instr)
        elif isinstance(instr, Alloc):
            self.execAlloc(state, instr)
        elif isinstance(instr, Cmp):
            self.execCmp(state, instr)
        elif isinstance(instr, Print):
            self.execPrint(state, instr)
        elif isinstance(instr, Branch):
            self.execBranch(state, instr)
        elif isinstance(instr, Assert):
            self.execAssert(state, instr)
        elif isinstance(instr, Assume):
            self.execAssume(state, instr)
        elif isinstance(instr, BinaryOperation):
            self.execBinaryOp(state, instr)
        elif isinstance(instr, Call):
            self.execCall(state, instr)
        elif isinstance(instr, Return):
            ec = self.execRet(state, instr)
        else:
            raise NotImplementedError(str(instr))

        return ec
