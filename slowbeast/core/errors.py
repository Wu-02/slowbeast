class Error:
    """
    Generic error type that represents an error in execution
    of program (e.g., assertion violation, out-of-bound access to memory,
    etc.)
    """

    __slots__ = "type", "descr"

    UNKNOWN = 0
    ASSERTION_FAIL = 1
    MEM_ERROR = 2
    GENERIC = 3

    def __init__(self, t, d=None):
        self.type = t
        self.descr = d

    def getType(self):
        return self.type

    def getDescr(self):
        return self.descr

    def isMemError(self):
        return self.type == Error.MEM_ERROR

    def isAssertionFail(self):
        return self.type == Error.ASSERTION_FAIL

    def __repr__(self):
        if self.type == Error.UNKNOWN:
            detail = "unknown error"
        elif self.type == Error.ASSERTION_FAIL:
            detail = "assertion failure"
        elif self.type == Error.MEM_ERROR:
            detail = "memory error"
        elif self.type == Error.GENERIC:
            detail = "error"
        else:
            raise RuntimeError("Invalid error type")

    def __str__(self):
        if self.descr:
            return "{0}: {1}".format(self.__repr__(), self.descr)
        return self.__repr__()


class AssertFailError(Error):
    def __init__(self, descr=None):
        super(AssertFailError, self).__init__(Error.ASSERTION_FAIL, descr)


class GenericError(Error):
    def __init__(self, descr=None):
        super(GenericError, self).__init__(Error.GENERIC, descr)


class MemError(Error):
    """
    Memory errors like invalid pointer dereference or out-of-bound
    access to memory.
    """

    __slots__ = "memerr"

    OOB_ACCESS = 1
    UNINIT_READ = 2
    INVALID_OBJ = 3

    def __init__(self, t, descr=None):
        super(MemError, self).__init__(Error.MEM_ERROR, descr)
        self.memerr = t

    def isUninitRead(self):
        return self.memerr == MemError.UNINIT_READ

    def isOobAccess(self):
        return self.memerr == MemError.OOB_ACCESS

    def isInvalidObj(self):
        return self.memerr == MemError.INVALID_OBJ

    def __repr__(self):
        assert self.isMemError()
        if self.memerr == MemError.OOB_ACCESS:
            detail = "oob"
        elif self.memerr == MemError.UNINIT_READ:
            detail = "uninitialized read"
        elif self.memerr == MemError.INVALID_OBJ:
            detail = "invalid object"
        else:
            raise RuntimeError("Invalid memory error type")

        return "memory error - {1}".format(super(MemError, self).__repr__(), detail)

    def __str__(self):
        return "{0} ({1})".format(self.__repr__(), self.getDescr())
