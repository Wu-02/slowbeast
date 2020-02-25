
class Error:
    """
    Generic error type that represents an error in execution
    of program (e.g., assertion violation, out-of-bound access to memory,
    etc.)
    """
    __slots__ = 'type', 'descr'

    UNKNOWN = 0
    ASSERTION_FAIL = 1
    MEMORY_ERROR = 2
    GENERIC = 3

    def __init__(self, t, d = None):
        self.type = t
        self.descr = d

    def getType(self):
        return self.type

    def getDescr(self):
        return self.descr

    def isMemoryError(self):
        return self.type == Error.MEMORY_ERROR

    def isAssertionFail(self):
        return self.type == Error.ASSERTION_FAIL

    def __repr__(self):
        if self.type == Error.UNKNOWN:
            return 'unknown error'
        elif self.type == Error.ASSERTION_FAIL:
            return 'assertion failure'
        elif self.type == Error.MEMORY_ERROR:
            return 'memory error'
        elif self.type == Error.GENERIC:
            return 'error'
        else:
            raise RuntimeError("Invalid error type")

class AssertFailError(Error):
    def __init__(self, descr = None):
        super(AssertFailError, self).__init__(Error.ASSERTION_FAIL, descr)

class GenericError(Error):
    def __init__(self, descr = None):
        super(GenericError, self).__init__(Error.GENERIC, descr)

class MemoryError(Error):
    """
    Memory errors like invalid pointer dereference or out-of-bound
    access to memory.
    """

    __slots__ = 'memerr'

    OOB_ACCESS = 1
    UNINIT_READ = 2
    INVALID_OBJ = 3
    
    def __init__(self, t, descr = None):
        super(MemoryError, self).__init__(Error.MEMORY_ERROR, descr)
        self.memerr = t
    
    def __repr__(self):
        assert self.isMemoryError()
        if self.memerr == OOB_ACCESS:
            detail = 'oob'
        elif self.memerr == UNINIT_READ:
            detail = 'uninitialized read'
        elif self.memerr == INVALID_OBJ:
            detail = 'invalid object'
        else:
            raise RuntimeError("Invalid memory error type")

        return "{0} ({1})".format(super(MemoryError, self).__repr__(), detail)

