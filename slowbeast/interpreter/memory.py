import sys
from copy import deepcopy
from .. util.debugging import dbg, FIXME

from . errors import ExecutionError
from .. ir.value import *
from .. ir.types import OffsetType


class MemoryObject:
    ids = 0

    def __init__(self, size, nm="unnamed"):
        MemoryObject.ids += 1
        self._id = MemoryObject.ids

        self.values = {}  # until we support composite objects, use just 'value'
        self.size = size
        self.name = nm  # for debugging
        self.allocation = None  # which allocation allocated this memory

    def copy(self):
        FIXME('add COW for memory objects')
        return deepcopy(self)

    def __eq__(self, rhs):
        return self._id == rhs._id

    def getID(self):
        return self._id

    def getSize(self):
        return self.size

    def setAllocation(self, a):
        self.allocation = a

    def write(self, x, off=Constant(0, OffsetType)):
        assert off.isConstant(), "Write to non-constant offset"
        assert isinstance(x, Value)
        offval = off.getValue()
        if offval != 0:
            FIXME("check that writes to MO do not overlap")
        if x.getByteWidth() > self.getSize().getValue() + offval:
            raise ExecutionError(
                "Written value too big for the object. Writing {0} B to offset {1} of {2}B object".format(
                    x.getByteWidth(), off, self.getSize()))
        self.values[offval] = x

    def read(self, bts, off=Constant(0, OffsetType)):
        assert off.isConstant(), "Read from non-constant offset"
        assert isinstance(bts, int), "Read non-constant number of bytes"
        offval = off.getValue()

        if self.getSize().getValue() < bts:
            return None, ExecutionError(
                "Read {0}B from object of size {1}B".format(
                    bts, self.getSize()))

        val = self.values.get(offval)
        if val is None:
            return None, ExecutionError(
                "Read from uninitialized memory or unaligned read (not supp. yet).")

        return val, None

    def getOffsets(self):
        """ Get offsets on which something is written """
        return self.values.keys()

    def __eq__(self, oth):
        return self._id == oth._id

    def __str__(self):
        s = "mo{0} ({1}, alloc'd by {2}), size: {3}".format(
            self._id,
            self.name if self.name else "no name",
            self.allocation.asValue() if self.allocation else "unknown",
            self.getSize())
        for k, v in self.values.items():
            s += "\n  {0} -> {1}".format(k, v)
        return s

    def asValue(self):
        return "mo{0}".format(self._id)

    def dump(self, stream=sys.stdout):
        stream.write(str(self))
        stream.write('\n')


class Memory:
    def __init__(self):
        self._objects = []

    def copy(self):
        FIXME('add COW for memory objects')
        return deepcopy(self)

    def __eq__(self, rhs):
        return self._objects == rhs._objects

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

    def dump(self, stream=sys.stdout):
        for o in self._objects:
            o.dump(stream)
