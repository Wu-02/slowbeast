from .. ir.value import Constant
from . memory import Memory
from .. core.callstack import CallStack
from . errors import ExecutionError
from copy import deepcopy
from sys import stdout


class ExecutionStatus:
    READY = 1      # ready for execution
    EXITED = 2     # normally exited
    TERMINATED = 3  # terminated by instruction (abort, etc.)
    ERROR = 4      # hit an error (violated assertion, oob access, etc.)
    # hit some problem in slowbeast (e.g., unsupported instruction, etc.)
    KILLED = 5

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

    def setKilled(self, e):
        # raise RuntimeError(e) # for debugging
        self.detail = e
        self.value = ExecutionStatus.KILLED

    def setExited(self, ec):
        self.detail = ec
        self.value = ExecutionStatus.EXITED

    def setTerminated(self, reason):
        # The state terminated for some other reason than regular exit
        self.detail = reason
        self.value = ExecutionStatus.TERMINATED

    def isError(self):
        return self.value == ExecutionStatus.ERROR

    def isKilled(self):
        return self.value == ExecutionStatus.KILLED

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
        elif self.value == ExecutionStatus.KILLED:
            return 'KILLED'
        raise RuntimeError("Invalid state status")

    def dump(self, stream=stdout):
        stream.write('status: {0}\n'.format(str(self)))


class ExecutionState:
    def __init__(self, pc=None, m=Memory(), glob={}):
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        self.globals = glob
        # globals FIXME: move to memory (with call stack)
        # callstack containing top-level values for the current
        # function (values of computation of instructions)
        # FIXME: move callstack to memory?
        # ...We create it redundantly when copying child classes
        self.cs = CallStack()
        # status of the execution: ready/exited/errored/etc.
        self.status = ExecutionStatus()

    def havoc(self):
        self.memory.havoc()
        self.cs.havoc()

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
        self.cs.set(what, v)

    def get(self, v):
        """ Get a value from a register (in the current stack frame) """
        ret = self.globals.get(v)
        if ret is None:
            ret = self.cs.get(v)
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
        self.cs.push(callsite, fun, argsMapping)
        self.pc = fun.getBBlock(0).getInstruction(0)

    def popCall(self):
        return self.cs.pop()

    def dump(self, stream=stdout):
        stream.write("---- State ----\n")
        self.status.dump(stream)
        stream.write(" -- program counter --\n")
        stream.write('{0}\n'.format(self.pc))
        stream.write("-- Globals:\n")
        for g, v in self.globals.items():
            stream.write("{0} -> {1}\n".format(g.asValue(), v.asValue()))
        stream.write("-- Call stack:\n")
        self.cs.dump(stream)
        stream.write("-- Memory:\n")
        self.memory.dump(stream)
