from sys import stdout
from copy import deepcopy, copy
from .. util.debugging import FIXME

from .. ir.value import Constant, Value
from .. ir.types import OffsetType
from .. core.errors import MemError


class MemoryObject:
    ids = 0

    __slots__ = '_id', 'values', 'size', 'name', 'allocation', '_ro'

    def __init__(self, size, nm="unnamed", objid=None):
        if objid:
            self._id = objid
        else:
            MemoryObject.ids += 1  # shift the objects counter for the next object
            self._id = MemoryObject.ids

        self.values = {}  # until we support composite objects, use just 'value'
        self.size = size
        self.name = nm  # for debugging
        self.allocation = None  # which allocation allocated this memory

        self._ro = False  # COW support

    def _setRO(self):
        self._ro = True

    def _isRO(self):
        return self._ro

    def writableCopy(self):
        new = copy(self)
        new.values = copy(self.values)
        new._ro = False
        return new

    def __eq__(self, rhs):
        return self._id == rhs._id

    def getID(self):
        return self._id

    def getSize(self):
        return self.size

    def setAllocation(self, a):
        self.allocation = a

    def write(self, x, off=Constant(0, OffsetType)):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if not off.isConstant():
            raise NotImplementedError(
                "Write to non-constant offset not supported")

        if not self.getSize().isConstant():
            raise NotImplementedError(
                "Write to symbolic-sized objects not implemented yet")

        offval = off.getValue()
        if offval != 0:
            FIXME("check that writes to MO do not overlap")
        if x.getByteWidth() > self.getSize().getValue() + offval:
            return MemError(MemError.OOB_ACCESS,
                            "Written value too big for the object. "
                            "Writing {0}B to offset {1} of {2}B object".format(
                                x.getByteWidth(), off, self.getSize()))
        self.values[offval] = x
        return None

    def read(self, bts, off=Constant(0, OffsetType)):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"

        if not off.isConstant():
            raise NotImplementedError(
                "Read from non-constant offset not supported")

        if not self.getSize().isConstant():
            raise NotImplementedError(
                "Read from symbolic-sized objects not implemented yet")

        offval = off.getValue()

        if self.getSize().getValue() < bts:
            return None, MemError(MemError.OOB_ACCESS,
                                  "Read {0}B from object of size {1}B".format(
                                      bts, self.getSize()))

        val = self.values.get(offval)
        if val is None:
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read from uninitialized memory (or unaligned read (not supp.  yet)).\n"
                f"Reading bytes {offval}-{offval+bts-1} from obj {self._id} with contents:\n"
                f"{self.values}")

        return val, None

    def getOffsets(self):
        """ Get offsets on which something is written """
        return self.values.keys()

    def __eq__(self, oth):
        return self._id == oth._id

    def __str__(self):
        s = "mo{0} ({1}, alloc'd by {2}, ro:{3}), size: {4}".format(
            self._id,
            self.name if self.name else "no name",
            self.allocation.asValue() if self.allocation else "unknown",
            self._ro, self.getSize())
        for k, v in self.values.items():
            s += "\n  {0} -> {1}".format(k, v)
        return s

    def asValue(self):
        return "mo{0}".format(self._id)

    def dump(self, stream=stdout):
        stream.write(str(self))
        stream.write('\n')
