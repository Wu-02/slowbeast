from slowbeast.ir.types import OffsetType, IntType, Bytes
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.domains.value import Value
from slowbeast.core.errors import MemError
from slowbeast.util.debugging import dbg, dbgv
from slowbeast.core.memory import Memory as CoreMemory
from slowbeast.core.memoryobject import MemoryObject as CoreMO
from slowbeast.solvers.solver import getGlobalExprManager

def get_byte(EM, x, bw, i):
    off = 8*i
    b = EM.Extract(
        x,
        ConcreteVal(off, OffsetType),
        ConcreteVal(off+7, OffsetType),
    )
    assert b.bitwidth() == 8
    return b

def write_bytes(offval, values, size, x):
    EM = getGlobalExprManager()
    bw = x.bytewidth()
    if not x.is_int():
        # rename to Cast and Cast to ReinterpretCast
        newx = EM.BitCast(x, IntType(8*bw))
        if newx is None:
            return MemError(MemError.UNSUPPORTED,
                            f"Cast of {x} to i{bw} is unsupported")
        x = newx
    n = 0
    for i in range(offval, offval + bw):
        b = get_byte(EM, x, bw, n)
        values[i] = b
        n += 1
    return None

def read_bytes(values, offval, size, bts):
    assert bts > 0, bts
    assert size > 0, bts
    assert offval >= 0, bts
    EM = getGlobalExprManager()
    if not all(values[i] for i in range(offval, offval + bts)):
        return None, MemError(MemError.UNINIT_READ,
                              "Read of uninitialized byte")
    c = offval + bts - 1
    # FIXME hack
    # just make Extract return Bytes and it should work well then
    val = EM.Concat(*(values[c - i] for i in range(0, bts)))
    val._type = Bytes(val.bytewidth())
    return val, None

def mo_to_bytes(values, size):
    dbgv("Promoting MO to bytes", color="gray")
    newvalues = [None] * size
    for o, val in values.items():
        tmp = write_bytes(o, newvalues, size, val)
        if not tmp is None:
            return None, tmp
    return newvalues, None

MAX_BYTES_SIZE = 64
class MemoryObject(CoreMO):
    # FIXME: refactor
    def read(self, bts, off=ConcreteVal(0, OffsetType)):
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"

        if not off.is_concrete():
            return None, MemError(MemError.UNSUPPORTED,
                                  "Read from non-constant offset not supported")

        size = self.getSize()
        if not size.is_concrete():
            return None, MemError(
                MemError.UNSUPPORTED,
                "Read from symbolic-sized objects not implemented yet"
            )

        assert size.is_int(), size
        offval = off.value()
        size = size.value()

        if size < bts:
            return None, MemError(
                MemError.OOB_ACCESS,
                f"Read {bts}B from object of size {size}"
            )

        values = self.values
        if isinstance(values, list):
            return read_bytes(values, offval, size, bts)

        val = values.get(offval)
        if val is None:
            if size <= MAX_BYTES_SIZE:
                values, err = mo_to_bytes(values, size)
                if err:
                    return None, err
                self.values = values
                return read_bytes(values, offval, size, bts)

            return None, MemError(
                MemError.UNINIT_READ,
                f"Uninitialized or unaligned read (the latter is unsupported)\n"
                f"Reading bytes {offval}-{offval+bts-1} from obj {self._id} with contents:\n"
                f"{values}",
            )

        valbw = val.bytewidth()
        if valbw != bts:
            if size <= MAX_BYTES_SIZE:
                values, err = mo_to_bytes(values, size)
                if err:
                    return None, err
                self.values = values
                return read_bytes(values, offval, size, bts)

            return None, MemError(
                MemError.UNSUPPORTED,
                f"Reading bytes from object defined by parts is unsupported atm: "
                f"reading {bts} bytes from off {offval} where is value with "
                f"{val.bytewidth()} bytes",
            )

        # FIXME: make me return Bytes objects (a sequence of bytes)
        return val, None

    def write(self, x, off=ConcreteVal(0, OffsetType)):
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if not off.is_concrete():
            return MemError(MemError.UNSUPPORTED,
                "Write to non-constant offset not supported")

        if not self.getSize().is_concrete():
            return MemError(MemError.UNSUPPORTED,
                "Write to symbolic-sized objects not implemented yet"
            )

        size = self.getSize().value()
        offval = off.value()

        if x.bytewidth() > size + offval:
         return MemError(
             MemError.OOB_ACCESS,
             "Written value too big for the object. "
             "Writing {0}B to offset {1} of {2}B object".format(
                 x.bytewidth(), offval, size
             ),
         )

        values = self.values
        if isinstance(values, list):
            return write_bytes(offval, values, size, x)
        else:
            # does the write overlap? should we promote the object
            # to bytes-object?
            # FIXME: not efficient...
            bw = x.bytewidth()
            for o, val in values.items():
                if offval < o + val.bytewidth() and offval + bw > o:
                    if size <= MAX_BYTES_SIZE: #For now...
                        # promote to bytes
                        tmp, err = mo_to_bytes(values, size)
                        if err:
                            return err
                        self.values = tmp
                        return write_bytes(offval, tmp, size, x)
                    return MemError(MemError.UNSUPPORTED,
                                    "Overlapping writes to memory")

            values[offval] = x
            return None
        return MemError(MemError.UNSUPPORTED, "Unsupported memory operation")

    def __repr__(self):
        s = "mo{0} ({1}, alloc'd by {2}, ro:{3}), size: {4}".format(
            self._id,
            self.name if self.name else "no name",
            self.allocation.as_value() if self.allocation else "unknown",
            self._ro,
            self.getSize(),
        )
        vals = self.values
        for k, v in (enumerate(vals) if isinstance(vals, list) else vals.items()):
            s += "\n  {0} -> {1}".format(k, v)
        return s


class Memory(CoreMemory):
    def createMO(self, size, nm=None, objid=None):
        """
        Create a new memory object -- may be overridden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid)
