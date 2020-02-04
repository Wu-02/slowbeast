from copy import copy
from .. util.debugging import dbg, FIXME
from .. interpreter.memory import Memory
from .. interpreter.memoryobject import MemoryObject
from .. domains.symbolic import SymbolicDomain

from .. ir.value import Constant, Value
from .. ir.types import OffsetType

class SEMemoryObject(MemoryObject):
    def __init__(self, array, size, nm=None):
        super(SEMemoryObject, self).__init__(size, nm)
        self.array = array

    def writableCopy(self):
        new = copy(self)
        new.values = copy(self.values)
        FIXME("se mo: don't we need a deep copy?")
        new.array = copy(self.array)
        new._ro = False
        return new

    def write(self, x, off=Constant(0, OffsetType)):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"
    
        FIXME("write: check OOB references")
        self.array = SymbolicDomain.Store(self.array, SymbolicDomain.lift(off), SymbolicDomain.lift(x))
        # add Store expr to updates
        return None

   #def read(self, bts, off=Constant(0, OffsetType)):
   #    """
   #    Read 'bts' bytes from offset 'off'. Return (value, None)
   #    on success otherwise return (None, error)
   #    """
   #    assert isinstance(bts, int), "Read non-constant number of bytes"
   #    FIXME("read: check OOB references and number of bytes")
   #    FIXME("read: concat all the bytes that we read")
   #    return None#... create select expr ...

   #def __str__(self):
   #    s = super(SEMemoryObject, self).__str__()
   #    return s

class SEMemoryObjectsManager:
    def __init__(self, exprmanager):
        self.exprmanager = exprmanager

    def allocate(self, size, nm=None):
        """ Allocate memory object of the right type """
        #FIXME: 8 is the size of bytes, but we could do that configurable
        return SEMemoryObject(self.exprmanager.freshArray("mo" if nm is None else nm, 8), size, nm)

class SymbolicMemory(Memory):
    def __init__(self, solver):
        super(SymbolicMemory, self).__init__(SEMemoryObjectsManager(solver.getExprManager()))
        self._solver = solver

    def copy(self):
        new = copy(self)
        new._solver = self._solver
        super(SymbolicMemory, self).copyTo(new)
        assert new == self, "BUG in copying object"
        return new

    def __eq__(self, rhs):
        return super(SymbolicMemory, self).__eq__(rhs) and\
            self._solver is rhs._solver

