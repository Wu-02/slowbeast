from copy import copy
from sys import stdout
from typing import Union, Optional, TextIO

from slowbeast.core.errors import MemError
from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import Alloc, GlobalVariable
from slowbeast.ir.types import get_offset_type


class MemoryObject:
    ids = 0

    __slots__ = (
        "_id",
        "_values",
        "_size",
        "_name",
        "_allocation",
        "_ro",
        "_is_heap",
        "_is_global",
        "_zeroed",
        "_read_only",
    )

    def __init__(
        self,
        size: ConcreteBitVec,
        nm: str = "unnamed",
        objid: None = None,
        is_heap: bool = False,
        is_global: bool = False,
        is_read_only: bool = False,
    ) -> None:
        if objid:
            self._id = objid
        else:
            MemoryObject.ids += 1  # shift the objects counter for the next object
            self._id = MemoryObject.ids

        self._values = {}  # until we support composite objects, use just 'value'
        self._size = size
        self._name = nm  # for debugging
        self._allocation = None  # which allocation allocated this memory
        self._is_global = is_global
        self._is_heap = is_heap
        self._zeroed = False
        self._read_only = is_read_only

        self._ro = False  # COW support

    def _set_ro(self) -> None:
        self._ro = True

    def _is_ro(self) -> bool:
        return self._ro

    def set_zeroed(self) -> None:
        self._zeroed = True

    def is_zeroed(self) -> bool:
        return self._zeroed

    def set_read_only(self) -> None:
        self._read_only = True

    def is_read_only(self) -> bool:
        return self._read_only

    def is_global(self) -> bool:
        return self._is_global

    def is_heap(self) -> bool:
        return self._is_heap

    def clear(self) -> None:
        assert not self._ro
        self._values.clear()

    def writable_copy(self) -> "MemoryObject":
        new = copy(self)
        new._values = copy(self._values)
        new._ro = False
        return new

    def clean_copy(self) -> "MemoryObject":
        new = copy(self)
        new._values = {}
        new._ro = False
        return new

    def __eq__(self, rhs: object):
        return isinstance(rhs, MemoryObject) and self._id == rhs._id

    def get_id(self) -> int:
        return self._id

    def size(self) -> ConcreteBitVec:
        return self._size

    def set_allocation(self, a: Union[Alloc, GlobalVariable]) -> None:
        self._allocation = a

    def allocation(self):
        return self._allocation

    def _has_concrete_size(self) -> bool:
        sz = self._size
        return sz is not None and sz.is_concrete()

    def _is_oob(self, bytesnum, offval: int = 0):
        sz = self._size
        return sz is None or bytesnum > sz.value() + offval

    def write(self, x: Value, off=None) -> Optional[MemError]:
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if not off.is_concrete():
            return MemError(
                MemError.UNSUPPORTED, "Write to non-constant offset not supported"
            )

        if not self._has_concrete_size():
            return MemError(
                MemError.UNSUPPORTED, "Write to symbolic-sized objects not implemented"
            )
        offval = 0 if off is None else off.value()
        if offval != 0:
            # FIXME: not efficient...
            bw = x.bytewidth()
            for o, val in self._values.items():
                if offval < o + val.bytewidth() and offval + bw > o:
                    return MemError(
                        MemError.UNSUPPORTED,
                        "Writing overlapping values to an object is not supported yet",
                    )
        if self._is_oob(x.bytewidth(), offval):
            return MemError(
                MemError.OOB_ACCESS,
                "Written value too big for the object. "
                "Writing {0}B to offset {1} of {2}B object".format(
                    x.bytewidth(), off, self._size
                ),
            )
        self._values[offval] = x
        return None

    def read(self, bts: int, off: Optional[ConcreteVal] = None):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"
        if off is None:
            off = ConcreteBitVec(0, get_offset_type())

        if not off.is_concrete():
            raise NotImplementedError("Read from non-constant offset not supported")

        if not self._has_concrete_size():
            return None, MemError(
                MemError.UNSUPPORTED,
                "Read from symbolic-sized objects not implemented yet",
            )

        offval = off.value()

        if self._is_oob(bts):
            return None, MemError(
                MemError.OOB_ACCESS,
                f"Read {bts}B from object of size {self._size}B",
            )

        val = self._values.get(offval)
        if val is None:
            if self._is_global and self._allocation.is_zeroed():
                return ConcreteBitVec(0, bts * 8), None
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read from uninitialized memory (or unaligned read (not supp.  yet)).\n"
                f"Reading bytes {offval}-{offval + bts - 1} from obj {self._id} with contents:\n"
                f"{self._values}",
            )

        # we would need to obtain overlapping offsets
        if val.bytewidth() != bts:
            return None, MemError(
                MemError.UNSUPPORTED,
                f"Reading bytes from object defined by parts is unsupported atm: "
                f"reading {bts} bytes from off {offval} where is value with "
                f"{val.bytewidth()} bytes",
            )

        # FIXME: make me return BytesType objects (a sequence of bytes)
        return val, None

    def offsets(self):
        """Get offsets on which something is written"""
        return self._values.keys()

    def _repr_header(self) -> str:
        nm = self._name if self._name else "<unnamed>"
        alloc = self._allocation.as_value() if self._allocation else "<unknown>"
        s = (
            f"mo{self._id} ('{nm}', alloc'd by {alloc}), "
            f"{'global, ' if self._is_global else ''}"
            f"{'heap, ' if self._is_heap else ''}"
            f"{'read-only, ' if self._read_only else ''}"
            f"{'zeroed, ' if self._zeroed else ''}"
            f"size: {self._size}"
        )
        return s

    def __repr__(self) -> str:
        s = self._repr_header()
        for k, v in self._values.items():
            s += f"\n  {k} -> {v}"
        return s

    def as_value(self) -> str:
        return f"mo{self._id}"

    def dump(self, stream: TextIO = stdout) -> None:
        stream.write(str(self))
        stream.write("\n")
