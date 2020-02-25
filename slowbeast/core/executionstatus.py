from copy import deepcopy
from sys import stdout

class ExecutionStatus:
    READY = 1      # ready for execution
    EXITED = 2     # normally exited
    TERMINATED = 3  # terminated by instruction (abort, etc.)
    ERROR = 4      # hit an error (violated assertion, oob access, etc.)
    # hit some problem in slowbeast (e.g., unsupported instruction, etc.)
    KILLED = 5

    __slots__ = 'value', 'detail'

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


