from .. ir.value import Constant
from . memory import Memory
from . calls import CallStack
from . errors import ExecutionError

class ExecutionStatus:
    READY = 1
    EXITED = 2
    ERROR = 3

    def __init__(self, st = READY):
        self.value = st
        self.detail = None

    def getStatus(self):
        return self.value

    def getDetail(self):
        return self.detail

    def setError(self, e):
        self.detail = e
        self.value = ExecutionStatus.ERROR

    def setExited(self, ec):
        self.detail = ec
        self.value = ExecutionStatus.EXITED

    def isError(self):
        return self.value == ExecutionStatus.ERROR

    def isExited(self):
        return self.value == ExecutionStatus.EXITED

    def isReady(self):
        return self.value == ExecutionStatus.READY

    def __str__(self):
        if self.value == ExecutionStatus.READY:
            return 'READY'
        elif self.value == ExecutionStatus.ERROR:
            return 'ERROR'
        elif self.value == ExecutionStatus.EXITED:
            return 'EXITED'
        assert False

    def dump(self):
        print('status: {0}'.format(str(self)))


class ExecutionState:
    def __init__(self, pc, m = Memory(), v = {}):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # state of the global memory
        # FIXME: move globals into memory
        self.globals = {}
        # callstack containing top-level values for the current
        # function (values of computation of instructions)
        self.cs = CallStack(v)
        # status of the execution: ready/exited/errored/etc.
        self.status = ExecutionStatus()

    def setError(self, e):
        self.pc = None
        self.status.setError(e)

    def hasError(self):
        return self.status.isError()

    def getError(self):
        assert self.hasError()
        return self.status.getDetail()

    def setExited(self, ec):
        self.pc = None
        self.status.setExited(ec)

    def exited(self):
        return self.status.isExited()

    def getExitCode(self):
        assert self.exited()
        return self.status.getDetail()

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

    def pushCall(self, callsite, fun, argsMapping = {}):
        self.cs.push(callsite, fun, argsMapping)
        self.pc = fun.getBBlock(0).getInstruction(0)

    def popCall(self):
        return self.cs.pop()

    def dump(self):
        print("---- State ----")
        self.status.dump()
        print("-- Call stack:")
        self.cs.dump()
        print("-- Memory:")
        self.memory.dump()
        print("-- -- -- -- -- -- -- --")


