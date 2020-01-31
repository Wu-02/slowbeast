from .. ir.value import Constant
from . memory import Memory
from . calls import CallStack
from . errors import ExecutionError
from copy import deepcopy


class ExecutionStatus:
    READY = 1
    EXITED = 2
    TERMINATED = 3
    ERROR = 4

    def __init__(self, st=READY):
        self.value = st
        self.detail = None

    def copy(self):
        return deepcopy(self)

    def __eq__(self, rhs):
        return self.value == rhs.value and self.detail == rhs.detail

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

    def setTerminated(self, reason):
        # The state terminated for some other reason than regular exit
        self.detail = reason
        self.value = ExecutionStatus.TERMINATED

    def isError(self):
        return self.value == ExecutionStatus.ERROR

    def isExited(self):
        return self.value == ExecutionStatus.EXITED

    def isTerminated(self):
        return self.value == ExecutionStatus.TERMINATED

    def isReady(self):
        return self.value == ExecutionStatus.READY

    def __repr__(self):
        if self.value == ExecutionStatus.READY:
            return 'READY'
        elif self.value == ExecutionStatus.ERROR:
            return 'ERROR'
        elif self.value == ExecutionStatus.EXITED:
            return 'EXITED'
        elif self.value == ExecutionStatus.TERMINATED:
            return 'TERMINATED'
        raise RuntimeError("Invalid state status")

    def dump(self):
        print('status: {0}'.format(str(self)))


class ExecutionState:
    def __init__(self, pc=None, m=Memory(), v={}):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # callstack containing top-level values for the current
        # function (values of computation of instructions)
        self.cs = CallStack(v)
        # status of the execution: ready/exited/errored/etc.
        self.status = ExecutionStatus()

    def __eq__(self, rhs):
        if self is rhs:
            return True
        assert self.pc is not None and\
            rhs.pc is not None
        return self.pc == rhs.pc and\
            self.status == rhs.status and\
            self.cs == rhs.cs and\
            self.memory == rhs.memory

    def copyTo(self, rhs):
        assert isinstance(rhs, ExecutionState)
        rhs.pc = self.pc
        rhs.memory = self.memory.copy()
        rhs.cs = self.cs.copy()
        rhs.status = self.status.copy()

    def copy(self):
        new = ExecutionState()
        self.copyTo(new)
        return new

    def setError(self, e):
        self.status.setError(e)

    def hasError(self):
        return self.status.isError()

    def getError(self):
        assert self.hasError() or self.isTerminated()
        return self.status.getDetail()

    def setExited(self, ec):
        self.status.setExited(ec)

    def setTerminated(self, reason):
        self.status.setTerminated(reason)

    def isTerminated(self):
        return self.status.isTerminated()

    def exited(self):
        return self.status.isExited()

    def getExitCode(self):
        assert self.exited()
        return self.status.getDetail()

    def isReady(self):
        return self.status.isReady()

    def eval(self, v):
        if isinstance(v, Constant):
            return v
        value = self.get(v)
        if value is None:
            raise ExecutionError(
                "Use of uninitialized/unknown variable {0}".format(v))
        return value

    def set(self, what, v):
        self.cs.set(what, v)

    def get(self, v):
        ret = self.cs.get(v)
        # if ret is None:
        #    ret = self.globals.get(v)
        return ret

    def pushCall(self, callsite, fun, argsMapping={}):
        self.cs.push(callsite, fun, argsMapping)
        self.pc = fun.getBBlock(0).getInstruction(0)

    def popCall(self):
        return self.cs.pop()

    def dump(self):
        print("---- State ----")
        self.status.dump()
        print(" -- program counter --")
        self.pc.dump()
        print("-- Call stack:")
        self.cs.dump()
        print("-- Memory:")
        self.memory.dump()
