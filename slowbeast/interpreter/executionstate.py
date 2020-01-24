from .. ir.value import Constant
from . memory import Memory
from . calls import CallStack

class ExecutionState:
    def __init__(self, pc, m = Memory(), v = {}):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # state of the global memory
        self.globals = {}
        # callstack containing top-level values for the current
        # function (values of computation of instructions)
        self.cs = CallStack(v)

    def eval(self, v):
        if isinstance(v, Constant):
            return v
        value = self.get(v)
        if value is None:
            raise ExecutionError("Use of uninitialized variable {0}".format(v))
        return value

    def set(self, what, v):
        self.cs.set(what, v)

    def get(self, v):
        ret = self.cs.get(v)
        if ret is None:
            ret = self.globals.get(v)
        return ret

    def call(self, callsite, fun, argsMapping = {}):
        self.cs.push(callsite, fun, argsMapping)
        return fun.getBBlock(0).getInstruction(0)

    def ret(self):
        return self.cs.pop()

