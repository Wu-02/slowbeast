from ..domains.concrete import ConcreteVal
from ..core.executionstatus import ExecutionStatus
from sys import stdout

#from slowbeast.util.debugging import dbgv


class ExecutionState:
    __slots__ = ["pc", "memory", "status"]

    def __init__(self, pc, m):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # status of the execution: ready/exited/errored/etc.
        self.status = ExecutionStatus()

    def __eq__(self, rhs):
        if self is rhs:
            return True
        assert self.pc is not None and rhs.pc is not None
        return (
            self.pc == rhs.pc
            and self.status == rhs.status
            and self.memory == rhs.memory
        )

    def copyTo(self, rhs):
        assert isinstance(rhs, ExecutionState)
        rhs.pc = self.pc
        rhs.memory = self.memory.copy()
        rhs.status = self.status.copy()

    def copy(self):
        new = ExecutionState(None, None)
        self.copyTo(new)
        return new

    def getStatusDetail(self):
        return self.status.getDetail()

    def setError(self, e):
        self.status.setError(e)

    def hasError(self):
        return self.status.isError()

    def wasKilled(self):
        return self.status.isKilled()

    def setKilled(self, e):
        self.status.setKilled(e)

    def getError(self):
        assert self.hasError() or self.isTerminated() or self.wasKilled()
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

    def getStatus(self):
        return self.status

    def isReady(self):
        return self.status.isReady()

    def eval(self, v):
        if isinstance(v, ConcreteVal):
            return v
        value = self.get(v)
        if value is None:
            raise RuntimeError(f"Use of uninitialized/unknown variable {v}")
        return value

    def try_eval(self, v):
        if isinstance(v, ConcreteVal):
            return v
        return self.get(v)

    def set(self, what, v):
        """ Associate a value to a register (in the current stack frame) """
       #if __debug__:
       #    dbgv("[{0}] -> {1} ({2})".format(what, v, v.type()), color="GREEN")
        # XXX: rename to bind?
        self.memory.set(what, v)

    def get(self, v):
        """
        Get a value from a register (in the current stack frame or globals)
        """
        return self.memory.get(v)

    def globalsList(self):
        """ Return the list of globals in this state """
        return self.memory.globalsList()

    def getValuesList(self):
        return self.memory.getValuesList()

    def pushCall(self, callsite, fun=None, argsMapping=None):
        """
        Push a new frame to the call stack. Callsite and fun can be None
        in the cases where we create dummy states and we just need some
        frame on the stack.
        """
        assert fun or not callsite, "Got no fun by some callsite..."
        self.memory.pushCall(callsite, fun, argsMapping or {})
        if fun:
            self.pc = fun.getBBlock(0).instruction(0)

    def popCall(self):
        return self.memory.popCall()

    def dump(self, stream=stdout):
        stream.write("---- State ----\n")
        self.status.dump(stream)
        stream.write(" -- program counter --\n")
        stream.write("{0}\n".format(self.pc))
        stream.write("-- Memory:\n")
        self.memory.dump(stream)
