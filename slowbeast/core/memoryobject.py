from sys import stdout
from copy import copy
from ..util.debugging import FIXME

from slowbeast.domains.value import Value
from ..domains.concrete import ConcreteVal
from ..ir.types import OffsetType
from ..core.errors import MemError


class MemoryObject:
    ids = 0

    __slots__ = "_id", "values", "size", "name", "allocation", "_ro"

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

    def get_id(self):
        return self._id

    def getSize(self):
        return self.size

    def setAllocation(self, a):
        self.allocation = a

    def write(self, x, off=ConcreteVal(0, OffsetType)):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if not off.is_concrete():
            raise NotImplementedError("Write to non-constant offset not supported")

        if not self.getSize().is_concrete():
            raise NotImplementedError(
                "Write to symbolic-sized objects not implemented yet"
            )

        offval = off.value()
        if offval != 0:
            FIXME("check that writes to MO do not overlap")
        if x.bytewidth() > self.getSize().value() + offval:
            return MemError(
                MemError.OOB_ACCESS,
                "Written value too big for the object. "
                "Writing {0}B to offset {1} of {2}B object".format(
                    x.bytewidth(), off, self.getSize()
                ),
            )
        self.values[offval] = x
        return None

    def read(self, bts, off=ConcreteVal(0, OffsetType)):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"

        if not off.is_concrete():
            raise NotImplementedError("Read from non-constant offset not supported")

        if not self.getSize().is_concrete():
            raise NotImplementedError(
                "Read from symbolic-sized objects not implemented yet"
            )

        offval = off.value()

        if self.getSize().value() < bts:
            return None, MemError(
                MemError.OOB_ACCESS,
                "Read {0}B from object of size {1}B".format(bts, self.getSize()),
            )

        val = self.values.get(offval)
        if val is None:
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read from uninitialized memory (or unaligned read (not supp.  yet)).\n"
                f"Reading bytes {offval}-{offval+bts-1} from obj {self._id} with contents:\n"
                f"{self.values}",
            )

        # we would need to obtain overlapping offsets
        if val.bytewidth() != bts:
            return None, MemError(
                MemError.UNSUPPORTED,
                f"Reading bytes from object defined by parts is unsupported atm: "
                f"reading {bts} bytes from off {offval} where is value with "
                f"{val.bytewidth()} bytes"
            )

        # FIXME: make me return Bytes objects (a sequence of bytes)
        return val, None

    def offsets(self):
        """ Get offsets on which something is written """
        return self.values.keys()

    def __eq__(self, oth):
        return self._id == oth._id

    def __str__(self):
        s = "mo{0} ({1}, alloc'd by {2}, ro:{3}), size: {4}".format(
            self._id,
            self.name if self.name else "no name",
            self.allocation.as_value() if self.allocation else "unknown",
            self._ro,
            self.getSize(),
        )
        for k, v in self.values.items():
            s += "\n  {0} -> {1}".format(k, v)
        return s

    def as_value(self):
        return "mo{0}".format(self._id)

    def dump(self, stream=stdout):
        stream.write(str(self))
        stream.write("\n")
