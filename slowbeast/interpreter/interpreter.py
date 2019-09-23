import sys 
from os.path import join, abspath, dirname
pth = join(dirname(__file__), '..')
sys.path.append(abspath(pth))

from ir.instruction import *
from . executionstate import ExecutionState
from . errors import ExecutionError
from . memory import Pointer

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
            return v.getValue()
        value = self._execs.get(v)
        if value is None:
            raise ExecutionError("Use of uninitialized variable {0}".format(v))
        return value

    def run(self):
        try:
            while self._execs:
                self.step()
        except ExecutionError as e:
            print("Execution error while executing '{0}': {1}".format(self._execs.pc, str(e)))
            self.dump()
        except Exception as e:
            self.dump()
            raise e

    def step(self):
        """ execute the current instruction and modify the state accordingly """
        instr = self._execs.pc
        # next instruction (may be overridden by commands
        nextInst = self._execs.pc.getNextInstruction()
        m = self._execs.memory

        # TODO: add an opcode to instruction and check only the opcode
        if isinstance(instr, Store):
            value = self.eval(instr.getValueOperand())
            to = self.eval(instr.getPointerOperand())
            assert isinstance(to, Pointer)
            to.object.write(value, to.offset)
        elif isinstance(instr, Load):
            frm = self.eval(instr.getPointerOperand())
            assert isinstance(frm, Pointer)
            self._execs.set(instr, frm.object.read(frm.offset))
        elif isinstance(instr, Alloc):
            o = self._execs.memory.allocate(instr.getSize())
            o.object.setAllocation(instr)
            self._execs.set(instr, o)
        elif isinstance(instr, Cmp):
            op1 = self.eval(instr.getOperand(0))
            op2 = self.eval(instr.getOperand(1))
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
            self._execs.set(instr, x)
        elif isinstance(instr, Print):
            for x in instr.getOperands():
                v = self.eval(x)
                sys.stdout.write(str(v))
        elif isinstance(instr, Branch):
            c = instr.getCondition()
            assert isinstance(c, ValueInstruction) or isinstance(c, Constant)
            cv = self.eval(instr.getCondition())

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
                if v != True:
                    raise ExecutionError("Assertion failed: {0} == {1} (!= True)".format(o, v))
        # assume is the same as assert during interpretation, but to make it different,
        # just make it dump the state and continue the execution
        elif isinstance(instr, Assume):
            for o in instr.getOperands():
                v = self.eval(o)
                if v != True:
                    print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                    self.dump()
                    break
        elif isinstance(instr, BinaryOperation):
            op1 = self.eval(instr.getOperand(0))
            op2 = self.eval(instr.getOperand(1))
            r = None
            if instr.getOperation() == BinaryOperation.ADD:
                r = op1 + op2
            elif instr.getOperation() == BinaryOperation.SUB:
                r = op1 - op2
            elif instr.getOperation() == BinaryOperation.MUL:
                r = op1 * op2
            elif instr.getOperation() == BinaryOperation.DIV:
                r = op1 / op2
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
                    sys.exit(ret)
                self._execs.set(rs, ret)
            nextInst = rs.getNextInstruction()
        else:
            raise NotImplementedError(str(instr))

        self._execs.pc = nextInst
        if self._execs.pc is None: # we have no other instruction to continue
            self.dump()
            self._execs = None

