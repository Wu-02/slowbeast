class Error:
    """
    Generic error type that represents an error in execution
    of program (e.g., assertion violation, out-of-bound access to memory,
    etc.)
    """

    __slots__ = "_type", "_descr"

    UNKNOWN = 0
    ASSERTION_FAIL = 1
    MEM_ERROR = 2
    GENERIC = 3

    def __init__(self, t, d=None):
        self._type = t
        self._descr = d

    def type(self):
        return self._type

    def getDescr(self):
        return self._descr

    def isMemError(self):
        return self._type == Error.MEM_ERROR

    def isAssertionFail(self):
        return self._type == Error.ASSERTION_FAIL

    def __repr__(self):
        ty = self._type
        if ty == Error.UNKNOWN:
            detail = "unknown error"
        elif ty == Error.ASSERTION_FAIL:
            detail = "assertion failure"
        elif ty == Error.MEM_ERROR:
            detail = "memory error"
        elif ty == Error.GENERIC:
            detail = "error"
        else:
            raise RuntimeError("Invalid error type")
        return detail

    def __str__(self):
        if self._descr:
            return f"{self.__repr__()}: {self._descr}"
        return self.__repr__()


class AssertFailError(Error):
    def __init__(self, descr=None):
        super().__init__(Error.ASSERTION_FAIL, descr)


class GenericError(Error):
    def __init__(self, descr=None):
        super().__init__(Error.GENERIC, descr)


class MemError(Error):
    """
    Memory errors like invalid pointer dereference or out-of-bound
    access to memory.
    """

    __slots__ = "_memerr"

    OOB_ACCESS = 1
    UNINIT_READ = 2
    INVALID_OBJ = 3

    def __init__(self, t, descr=None):
        super(MemError, self).__init__(Error.MEM_ERROR, descr)
        self._memerr = t

    def isUninitRead(self):
        return self._memerr == MemError.UNINIT_READ

    def isOobAccess(self):
        return self._memerr == MemError.OOB_ACCESS

    def isInvalidObj(self):
        return self._memerr == MemError.INVALID_OBJ

    def __repr__(self):
        err = self._memerr
        assert self.isMemError()
        if err == MemError.OOB_ACCESS:
            detail = "oob"
        elif err == MemError.UNINIT_READ:
            detail = "uninitialized read"
        elif err == MemError.INVALID_OBJ:
            detail = "invalid object"
        else:
            raise RuntimeError("Invalid memory error type")

        return "memory error - {1}".format(super(MemError, self).__repr__(), detail)

    def __str__(self):
        return "{0} ({1})".format(self.__repr__(), self.getDescr())
