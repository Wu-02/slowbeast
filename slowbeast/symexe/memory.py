from copy import deepcopy
from .. util.debugging import dbg, FIXME
from .. interpreter.memory import Memory

#from .. errors import ExecutionError
#from .. ir.value import *
#from .. ir.types import OffsetType


class SymbolicMemory(Memory):
    def __init__(self, solver):
        super(SymbolicMemory, self).__init__()
        self._solver = solver

    def copy(self):
        FIXME('add COW for symbolic memory')
        new = super(SymbolicMemory, self).copy()
        new._solver = self._solver
        assert new == self, "BUG in copying object"
        return deepcopy(self)

    def __eq__(self, rhs):
        return super(SymbolicMemory, self).__eq__(rhs) and\
            self._solver is rhs._solver

   # def allocate(self, size, nm=None):
   #    o = MemoryObject(size, nm)
   #    self._objects.append(o)
   #    return Pointer(o)
