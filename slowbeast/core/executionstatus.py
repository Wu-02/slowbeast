from copy import deepcopy
from sys import stdout


class ExecutionStatus:
    READY = 1  # ready for execution
    EXITED = 2  # normally exited
    TERMINATED = 3  # terminated by instruction (abort, etc.)
    ERROR = 4  # hit an error (violated assertion, oob access, etc.)
    # hit some problem in slowbeast (e.g., unsupported instruction, etc.)
    KILLED = 5

    __slots__ = "_status", "_detail"

    def __init__(self, st=READY):
        self._status = st
        self._detail = None

    def copy(self):
        return deepcopy(self)

    def __eq__(self, rhs):
        return self._status == rhs._status and self._detail == rhs._detail

    def __hash__(self):
        return hash(self._detail) ^ hash(self._status)

    def getStatus(self):
        return self._status

    def getDetail(self):
        return self._detail

    def setError(self, e):
        self._detail = e
        self._status = ExecutionStatus.ERROR

    def setKilled(self, e):
        # raise RuntimeError(e) # for debugging
        self._detail = e
        self._status = ExecutionStatus.KILLED

    def setExited(self, ec):
        self._detail = ec
        self._status = ExecutionStatus.EXITED

    def setTerminated(self, reason):
        # The state terminated for some other reason than regular exit
        self._detail = reason
        self._status = ExecutionStatus.TERMINATED

    def isError(self):
        return self._status == ExecutionStatus.ERROR

    def isKilled(self):
        return self._status == ExecutionStatus.KILLED

    def isExited(self):
        return self._status == ExecutionStatus.EXITED

    def isTerminated(self):
        return self._status == ExecutionStatus.TERMINATED

    def isReady(self):
        return self._status == ExecutionStatus.READY

    def __repr__(self):
        val = self._status
        if val == ExecutionStatus.READY:
            return "READY"
        if val == ExecutionStatus.ERROR:
            return "ERROR"
        if val == ExecutionStatus.EXITED:
            return "EXITED"
        if val == ExecutionStatus.TERMINATED:
            return "TERMINATED"
        elif val == ExecutionStatus.KILLED:
            return "KILLED"
        raise RuntimeError("Invalid state status")

    def dump(self, stream=stdout):
        stream.write("status: {0}\n".format(str(self)))
