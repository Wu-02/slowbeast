from copy import copy
from .. util.debugging import dbg, FIXME
from .. interpreter.memory import Memory
from .. interpreter.memoryobject import MemoryObject

#from .. errors import ExecutionError
#from .. ir.value import *
#from .. ir.types import OffsetType


class SEMemoryObject(MemoryObject):
    def __init__(self, size, nm=None):
        super(SEMemoryObject, self).__init__(size, nm)

class SymbolicMemory(Memory):
    def __init__(self, solver):
        super(SymbolicMemory, self).__init__()
        self._solver = solver

    # override this method to create the right objects
    def createMO(self, size, nm=None):
        return SEMemoryObject(size, nm)

    def copy(self):
        new = copy(self)
        new._solver = self._solver
        super(SymbolicMemory, self).copyTo(new)
        assert new == self, "BUG in copying object"
        return new

    def __eq__(self, rhs):
        return super(SymbolicMemory, self).__eq__(rhs) and\
            self._solver is rhs._solver
