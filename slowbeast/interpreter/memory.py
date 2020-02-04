import sys
from copy import copy

from .. util.debugging import dbg, FIXME
from .. ir.value import *
from .. ir.types import OffsetType, SizeType

from . memoryobject import MemoryObject
from . errors import ExecutionError

class MemoryObjectsManager:
    def allocate(self, size, nm=None):
        """ Allocate memory object of the right type """
        return MemoryObject(size, nm)

class Memory:
    def __init__(self, momanager=MemoryObjectsManager()):
        self.momanager = momanager
        self._objects = {}
        self._objects_ro = False

    def copyTo(self, new):
        new.momanager = self.momanager
        new._objects = self._objects
        new._objects_ro = True
        self._objects_ro = True
        for o in self._objects.values():
            o._setRO()
        return new

    def copy(self):
        new = copy(self)
        new._objects_ro = True
        self._objects_ro = True
        for o in self._objects.values():
            o._setRO()
        return new

    def _cow_reown(self):
        if self._objects_ro:
            assert all([x._isRO() for x in self._objects.values()])
            self._objects = copy(self._objects)
            self._objects_ro = False

    def __eq__(self, rhs):
        return self._objects == rhs._objects

    def allocate(self, size, instr=None, nm=None):
        """ Allocate a new memory object and return a pointer to it """
        self._cow_reown()
        o = self.momanager.allocate(size, nm)
        assert o._isRO() is False, "Created object is read-only (COW bug)"
        o.setAllocation(instr)
        assert self._objects.get(o.getID()) is None
        self._objects[o.getID()] = o
        return Pointer(Constant(o.getID(), SizeType))

    def hasObject(self, moid):
        return self._objects.get(moid) is not None

    def write(self, ptr, x):
        self._cow_reown()
        obj = self._objects.get(ptr.getObject().getValue())
        if obj is None:
            return "Write to invalid object"
        if obj._isRO():  # copy on write
            obj = obj.writableCopy()
            assert not obj._isRO()
            self._objects[obj.getID()] = obj

        return obj.write(x, ptr.getOffset())

    def read(self, ptr, bytesNum):
        obj = self._objects.get(ptr.getObject().getValue())
        if obj is None:
            return "Read from invalid object"

        return obj.read(bytesNum, ptr.getOffset())

    def dump(self, stream=sys.stdout):
        for o in self._objects.values():
            o.dump(stream)
