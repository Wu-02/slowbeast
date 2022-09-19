from slowbeast.core.errors import MemError
from slowbeast.core.memoryobject import MemoryObject as CoreMO
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.value import Value
from slowbeast.ir.types import get_offset_type, BitVecType, Bytes
from slowbeast.solvers.symcrete import global_expr_mgr
from slowbeast.util.debugging import dbgv
from typing import List, Tuple, Optional, Sized
from typing_extensions import SupportsIndex


def get_byte(EM, x, bw, i: int):
    off = 8 * i
    b = EM.Extract(
        x,
        ConcreteVal(off, get_offset_type()),
        ConcreteVal(off + 7, get_offset_type()),
    )
    assert b.bitwidth() == 8
    return b


def write_bytes(offval, values, size, x) -> Optional[MemError]:
    EM = global_expr_mgr()
    bw = x.bytewidth()
    if not x.is_bv():
        # rename to Cast and Cast to ReinterpretCast
        newx = EM.BitCast(x, BitVecType(8 * bw))
        if newx is None:
            return MemError(
                MemError.UNSUPPORTED, f"Cast of {x} to i{bw} is unsupported"
            )
        x = newx
    n = 0
    for i in range(offval, offval + bw):
        b = get_byte(EM, x, bw, n)
        values[i] = b
        n += 1
    return None


def read_bytes(values: Sized, offval, size, bts, zeroed):
    assert bts > 0, bts
    assert size > 0, size
    assert offval >= 0, offval
    EM = global_expr_mgr()
    if zeroed:
        c = offval + bts - 1
        # just make Extract return Bytes and it should work well then
        val = EM.Concat(
            *(
                values[c - i] if values[c - i] else ConcreteVal(0, BitVecType(8))
                for i in range(0, bts)
            )
        )
        # FIXME hack
        val._type = Bytes(val.bytewidth())
    else:
        if offval + bts > len(values):
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read of {bts} bytes on offset {offval} "
                f"from object with {len(values)} initialized "
                "values.",
            )
        if not all(values[i] for i in range(offval, offval + bts)):
            return None, MemError(MemError.UNINIT_READ, "Read of uninitialized byte")
        c = offval + bts - 1
        # just make Extract return Bytes and it should work well then
        val = EM.Concat(*(values[c - i] for i in range(0, bts)))
        # FIXME hack
        val._type = Bytes(val.bytewidth())
    return val, None


def mo_to_bytes(
    values, size: SupportsIndex
) -> Tuple[Optional[List[None]], Optional[MemError]]:
    dbgv("Promoting MO to bytes", color="gray")
    newvalues = [None] * size
    for o, val in values.items():
        tmp = write_bytes(o, newvalues, size, val)
        if tmp is not None:
            return None, tmp
    # if __debug__:
    #    rval, err = read_bytes(newvalues, o, size, val.bytewidth(), False)
    #    assert err is None
    #    crval = global_expr_mgr().Cast(rval, val.type())
    #    assert val == crval, f"{cval} ({rval}) != {val}"
    return newvalues, None


MAX_BYTES_SIZE = 64


class MemoryObject(CoreMO):
    __slots__ = ()

    # FIXME: refactor
    def read(self, bts: int, off: Optional[ConcreteVal] = None):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"
        if off is None:
            off = ConcreteVal(0, get_offset_type())

        if not off.is_concrete():
            return None, MemError(
                MemError.UNSUPPORTED, "Read from non-constant offset not supported"
            )

        size = self.size()
        if not size.is_concrete():
            return None, MemError(
                MemError.UNSUPPORTED,
                "Read from symbolic-sized objects not implemented yet",
            )

        assert size.is_bv(), size
        offval = off.value()
        size = size.value()

        if size < bts:
            return None, MemError(
                MemError.OOB_ACCESS, f"Read {bts}B from object of size {size}"
            )

        values = self._values
        if isinstance(values, list):
            return read_bytes(values, offval, size, bts, self._zeroed)

        val = values.get(offval)
        if val is None:
            if size <= MAX_BYTES_SIZE:
                values, err = mo_to_bytes(values, size)
                if err:
                    return None, err
                self._values = values
                assert isinstance(self._values, list)
                return read_bytes(values, offval, size, bts, self._zeroed)

            if self._zeroed:
                return ConcreteVal(0, BitVecType(bts * 8)), None
            return None, MemError(
                MemError.UNINIT_READ,
                "uninitialized or unaligned read (the latter is unsupported)\n"
                f"Reading bytes {offval}-{offval + bts - 1} from obj {self._id} with contents:\n"
                f"{values}",
            )

        valbw = val.bytewidth()
        if valbw != bts:
            if size <= MAX_BYTES_SIZE:
                values, err = mo_to_bytes(values, size)
                if err:
                    return None, err
                self._values = values
                return read_bytes(values, offval, size, bts, self._zeroed)

            return None, MemError(
                MemError.UNSUPPORTED,
                "Reading bytes from object defined by parts is unsupported atm: "
                f"reading {bts} bytes from off {offval} where is value with "
                f"{val.bytewidth()} bytes",
            )

        # FIXME: make me return Bytes objects (a sequence of bytes)
        return val, None

    def write(self, x: Value, off: Optional[ConcreteVal] = None):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if off is None:
            off = ConcreteVal(0, get_offset_type())

        if not off.is_concrete():
            return MemError(
                MemError.UNSUPPORTED, "Write to non-constant offset not supported"
            )

        if not self.size().is_concrete():
            return MemError(
                MemError.UNSUPPORTED,
                "Write to symbolic-sized objects not implemented yet",
            )

        size = self.size().value()
        offval = off.value()

        if x.bytewidth() > size + offval:
            return MemError(
                MemError.OOB_ACCESS,
                "Written value too big for the object. "
                "Writing {0}B to offset {1} of {2}B object".format(
                    x.bytewidth(), offval, size
                ),
            )

        values = self._values
        if isinstance(values, list):
            return write_bytes(offval, values, size, x)
        else:
            # does the write overlap? should we promote the object
            # to bytes-object?
            # FIXME: not efficient...
            bw = x.bytewidth()
            for o, val in values.items():
                if offval < o + val.bytewidth() and offval + bw > o:
                    if o == offval and val.bytewidth() == bw:
                        break  # the overlap is perfect, we just overwrite
                        # the value
                    if size <= MAX_BYTES_SIZE:  # For now...
                        # promote to bytes
                        tmp, err = mo_to_bytes(values, size)
                        if err:
                            return err
                        self._values = tmp
                        return write_bytes(offval, tmp, size, x)
                    return MemError(
                        MemError.UNSUPPORTED, "Overlapping writes to memory"
                    )

            values[offval] = x
            return None
        return MemError(MemError.UNSUPPORTED, "Unsupported memory operation")

    def __repr__(self) -> str:
        s = "mo{0} ({1}, alloc'd by {2}, ro:{3}), 0-ed: {4}, size: {5}".format(
            self._id,
            self._name if self._name else "no name",
            self._allocation.as_value() if self._allocation else "unknown",
            self._ro,
            self._zeroed,
            self._size,
        )
        vals = self._values
        for k, v in enumerate(vals) if isinstance(vals, list) else vals.items():
            s += f"\n  {k} -> {v}"
        return s
