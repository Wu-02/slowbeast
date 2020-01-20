import sys
from os.path import join, abspath, dirname
pth = join(dirname(__file__), '..')
sys.path.append(abspath(pth))

from ir.instruction import *
from ir.value import *
from . executionstate import ExecutionState
from . errors import ExecutionError

class Interpreter:
    def __init__(self, program):
        self._program = program
        self._execs = ExecutionState(program.getEntry().getBBlock(0).getInstruction(0))

    def dump(self):
        print("-- Interpreter state --")
        print("-- Call stack:")
        self._execs.cs.dump()
        print("-- Memory:")
        self._execs.memory.dump()
        print("-- -- -- -- -- -- -- --")

    def eval(self, v):
        if isinstance(v, Constant):
            return v
        value = self._execs.get(v)
        if value is None:
            raise ExecutionError("Use of uninitialized variable {0}".format(v))
        return value

    def run(self, debug=False):
        try:
            while self._execs:
                self.step(debug)
        except ExecutionError as e:
            print("Execution error while executing '{0}': {1}".format(self._execs.pc, str(e)))
            self.dump()
        except Exception as e:
            print("Fatal error while executing '{0}'".format(self._execs.pc))
            self.dump()
            raise e

    def step(self, debug=False):
        """ execute the current instruction and modify the state accordingly """
        instr = self._execs.pc
        # next instruction (may be overridden by commands
        nextInst = self._execs.pc.getNextInstruction()
        m = self._execs.memory

        # debug print
        if debug:
            sys.stderr.write("[sb dbg]: {0}\n".format(instr))

        # TODO: add an opcode to instruction and check only the opcode
        if isinstance(instr, Store):
            value = self.eval(instr.getValueOperand())
            to = self.eval(instr.getPointerOperand())
            assert isinstance(to, Pointer)
            to.object.write(value, to.offset)
        elif isinstance(instr, Load):
            frm = self.eval(instr.getPointerOperand())
            assert isinstance(frm, Pointer)
            self._execs.set(instr, frm.object.read(instr.getBytesNum(), frm.offset))
        elif isinstance(instr, Alloc):
            o = self._execs.memory.allocate(instr.getSize().value)
            o.object.setAllocation(instr)
            self._execs.set(instr, o)
        elif isinstance(instr, Cmp):
            op1 = self.eval(instr.getOperand(0))
            op2 = self.eval(instr.getOperand(1))
            if isinstance(op1, Pointer):
                if not isinstance(op2, Pointer):
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
            self._execs.set(instr, Constant(x, 1))
        elif isinstance(instr, Print):
            for x in instr.getOperands():
                v = self.eval(x)
                if isinstance(v, Constant):
                    v = v.getValue()
                sys.stdout.write(str(v))
            sys.stdout.write('\n')
            sys.stdout.flush()
        elif isinstance(instr, Branch):
            c = instr.getCondition()
            assert isinstance(c, ValueInstruction) or isinstance(c, Constant)
            cv = self.eval(instr.getCondition()).value

            if cv == True:
                succ = instr.getTrueSuccessor()
            elif cv == False:
                succ = instr.getFalseSuccessor()
            else:
                raise ExecutionError("Indeterminite condition")

            assert succ
            if not succ.empty():
                nextInst = succ.getInstruction(0)
            else:
                assert nextInst is None
        elif isinstance(instr, Assert):
            for o in instr.getOperands():
                v = self.eval(o)
                assert isinstance(v, Constant)
                if v.getValue() != True:
                    raise ExecutionError("Assertion failed: {0} is {1} (!= True)".format(o, v))
        # assume is the same as assert during interpretation, but to make it different,
        # just make it dump the state and continue the execution
        elif isinstance(instr, Assume):
            for o in instr.getOperands():
                v = self.eval(o)
                assert isinstance(v, Constant)
                if v.getValue() != True:
                    print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                    self.dump()
                    break
        elif isinstance(instr, BinaryOperation):
            op1c = self.eval(instr.getOperand(0))
            op2c = self.eval(instr.getOperand(1))
            op1 = None
            op2 = None
            bw = max(op1c.getByteWidth(), op2c.getByteWidth())
            # if one of the operands is a pointer,
            # lift the other to pointer too
            if isinstance(op1c, Pointer):
                if not isinstance(op2c, Pointer):
                    assert isinstance(op2c, Constant)
                    # adding a constant -- create a pointer
                    # to the object with the right offset
                    op2c = Pointer(op1c.object, op2c.value)
            elif isinstance(op2c, Pointer):
                if not isinstance(op1c, Pointer):
                    assert isinstance(op1c, Constant)
                    # adding a constant -- create a pointer
                    # to the object with the right offset
                    op1c = Pointer(op2c.object, op1c.value)
            else:
                op1 = op1c.value
                op2 = op2c.value

            if isinstance(op1c, Pointer) and op1c.object != op2c.object:
                raise ExecutionError("Pointer arithmetic on unrelated pointers")

            r = None
            if instr.getOperation() == BinaryOperation.ADD:
                if isinstance(op1c, Pointer):
                    assert isinstance(op2c, Pointer)
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
                if isinstance(op1c, Pointer):
                    assert isinstance(op2c, Pointer)
                    r = Pointer(op1c.object, op1c.offset * op2c.offset)
                else:
                    r = Constant(op1 * op2)
            elif instr.getOperation() == BinaryOperation.DIV:
                if isinstance(op1c, Pointer):
                    assert isinstance(op2c, Pointer)
                    r = Pointer(op1c.object, op1c.offset / op2c.offset)
                else:
                    r = Constant(op1 / op2)
            else:
                raise NotImplementedError("Binary operation: " + str(instr))

            self._execs.set(instr, r)
        elif isinstance(instr, Call):
            fun = instr.getCalledFunction()
            # map values to arguments
            assert len(instr.getOperands()) == len(fun.getArguments())
            mapping = {x : self.eval(y) for (x, y)\
                       in zip(fun.getArguments(), instr.getOperands())}
            nextInst = self._execs.call(instr, fun, mapping)
        elif isinstance(instr, Return):
            if len(instr.getOperands()) == 0: # returns nothing
                rs = self._execs.ret()
            else:
                ret = self.eval(instr.getOperand(0))
                rs = self._execs.ret()
                if rs is None: # popped the last frame
                    if isinstance(ret, Pointer):
                        raise ExecutionError("Returnin a pointer from main")
                    assert isinstance(ret, Constant)
                    sys.exit(ret.getValue())
                self._execs.set(rs, ret)
            nextInst = rs.getNextInstruction()
        else:
            raise NotImplementedError(str(instr))

        self._execs.pc = nextInst
        if self._execs.pc is None: # we have no other instruction to continue
            self.dump()
            self._execs = None

