from .. ir.value import Constant
from . memory import Memory
from .. core.executionstatus import ExecutionStatus
from sys import stdout

class ExecutionState:
    def __init__(self, pc=None, m=Memory(), glob={}):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        self.globals = glob
        # status of the execution: ready/exited/errored/etc.
        self.status = ExecutionStatus()

    def __eq__(self, rhs):
        if self is rhs:
            return True
        assert self.pc is not None and\
            rhs.pc is not None
        return self.pc == rhs.pc and\
            self.status == rhs.status and\
            self.memory == rhs.memory

    def copyTo(self, rhs):
        assert isinstance(rhs, ExecutionState)
        rhs.pc = self.pc
        rhs.memory = self.memory.copy()
        rhs.status = self.status.copy()

    def copy(self):
        new = ExecutionState()
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
        if isinstance(v, Constant):
            return v
        value = self.get(v)
        if value is None:
            raise RuntimeError(
                "Use of uninitialized/unknown variable {0}".format(v))
        return value

    def bindGlobal(self, glob, ptr):
        self.globals[glob] = ptr

    def set(self, what, v):
        """ Associate a value to a register (in the current stack frame) """
       #from .. util.debugging import dbg
       #dbg("[{0}] -> {1} ({2})".format(what, v, v.getType()), color="GREEN")
        # XXX: rename to bind?
        self.memory.set(what, v)

    def get(self, v):
        """ Get a value from a register (in the current stack frame) """
        ret = self.globals.get(v)
        if ret is None:
            ret = self.memory.get(v)
        return ret

    def write(self, ptr, value):
        if not ptr.getOffset().isConstant():
            self.setKilled("Write with non-constant offset not supported yet")
            return [self]
        try:
            err = self.memory.write(ptr, value)
        except NotImplementedError as e:
            self.setKilled(str(e))
            return [self]
        if err:
            self.setError(err)
        return [self]

    def read(self, ptr, dest, bytesNum):
        assert isinstance(bytesNum, int), "Invalid number of bytes"
        if not ptr.getOffset().isConstant():
            self.setKilled("Read with non-constant offset not supported yet")
            return [self]
        try:
            val, err = self.memory.read(ptr, bytesNum)
        except NotImplementedError as e:
            self.setKilled(str(e))
            return [self]
        if err:
            self.setError(err)
        else:
            self.set(dest, val)
        return [self]

    def pushCall(self, callsite, fun, argsMapping={}):
        self.memory.pushCall(callsite, fun, argsMapping)
        self.pc = fun.getBBlock(0).getInstruction(0)

    def popCall(self):
        return self.memory.popCall()

    def dump(self, stream=stdout):
        stream.write("---- State ----\n")
        self.status.dump(stream)
        stream.write(" -- program counter --\n")
        stream.write('{0}\n'.format(self.pc))
        stream.write("-- Globals:\n")
        for g, v in self.globals.items():
            stream.write("{0} -> {1}\n".format(g.asValue(), v.asValue()))
        stream.write("-- Memory:\n")
        self.memory.dump(stream)
