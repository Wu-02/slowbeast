import sys
from . errors import ExecutionError
from .. ir.value import *
from .. ir.types import OffsetType


class MemoryObject:
    ids = 0

    def __init__(self, size, nm="unnamed"):
        MemoryObject.ids += 1
        self._id = MemoryObject.ids

        self.value = None  # until we support composite objects, use just 'value'
        self.size = size
        self.name = nm  # for debugging
        self.allocation = None  # which allocation allocated this memory

    def getID(self):
        return self._id

    def getSize(self):
        return self.size

    def setAllocation(self, a):
        self.allocation = a

    def write(self, x, off=Constant(0, OffsetType)):
        assert off.getValue() == 0, "Writes to relative offset unimplemented"
        assert isinstance(x, Value)
        if x.getByteWidth() > self.size:
            raise ExecutionError("Written value too big for the object")
        self.value = x

    def read(self, bts, off=Constant(0, OffsetType)):
        assert off.getValue() == 0, "Writes to relative offset unimplemented"
        if self.value is None:
            raise ExecutionError("Read from uninitialized variable")

        if self.size < bts:
            raise ExecutionError("Read {0} bytes from object of size {1}"
                                 .format(bts, self.size))
        return self.value

    def __eq__(self, oth):
        return self._id == oth._id

    def __str__(self):
        if hasattr(self.value, 'asValue'):
            v = self.value.asValue()
        else:
            v = self.value
        return "mo{0} ({1} alloc. by {2}), {3} -> {4}".format(self._id,
                                                              self.name,
                                                              self.allocation.asValue() if self.allocation else "unknown",
                                                              self.size,
                                                              v)

    def asValue(self):
        return "mo{0}".format(self._id)

    def dump(self):
        print(str(self))


class Memory:
    def __init__(self):
        self._objects = []

    def allocate(self, size, nm=None):
        o = MemoryObject(size, nm)
        self._objects.append(o)
        return Pointer(o)

    # def write(self, x, to):
    #     self._vars[to] = x

    # def read(self, frm):
    #     v = self._vars.get(frm)
    #     if v:
    #         return v

    #     raise ExecutionError("Read from uninitialized variable")
    #     return None

    def dump(self):
        for o in self._objects:
            o.dump()
