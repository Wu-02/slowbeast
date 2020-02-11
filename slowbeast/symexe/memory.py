from copy import copy
from .. util.debugging import dbg, FIXME
from .. interpreter.memory import Memory
from .. interpreter.memoryobject import MemoryObject

#from .. errors import ExecutionError
#from .. ir.value import *
from .. ir.types import OffsetType
from .. ir.value import Constant


class SEMemoryObject(MemoryObject):
    def __init__(self, size, nm=None):
        super(SEMemoryObject, self).__init__(size, nm)

   # def write(self, x, off=Constant(0, OffsetType)):
   #    return super(SEMemoryObject, self).write(x, off)

   # def read(self, bts, off=Constant(0, OffsetType)):
   #    return super(SEMemoryObject, self).read(bts, off)


class SymbolicMemory(Memory):
    def __init__(self, solver, uninit_nondet=False):
        super(SymbolicMemory, self).__init__()
        self._solver = solver
        self._uninit_is_nondet = uninit_nondet

    def setUninitializedIsNondet(self, b):
        self._uninit_is_nondet = b

    def uninitializedIsNondet(self):
        return self._uninit_is_nondet

    # override this method to create the right objects
    def createMO(self, size, nm=None):
        return SEMemoryObject(size, nm)

    def copy(self):
        new = copy(self)
        new._solver = self._solver
        new._uninit_is_nondet = self._uninit_is_nondet
        super(SymbolicMemory, self).copyTo(new)
        assert new == self, "BUG in copying object"
        return new

    def write(self, ptr, x):
        return super(SymbolicMemory, self).write(ptr, x)

    def read(self, ptr, bytesNum):
        val, err = super(SymbolicMemory, self).read(ptr, bytesNum)
        if err:
            if self.uninitializedIsNondet() and str(
                    err).startswith('Read from uninitialized'):
                dbg("Reading nondet for uninitialized value: {0}".format(ptr))
                val = self._solver.freshValue("uninit", 8 * bytesNum)
                # write the fresh value into memory, so that
                # later reads see the same value.
                # If an error occurs, just propagate it up
                err = self.write(ptr, val)
        return val, err

    def __eq__(self, rhs):
        return super(SymbolicMemory, self).__eq__(rhs) and\
            self._solver is rhs._solver
