from typing import Union, Tuple, Optional

from slowbeast.core.errors import MemError
from slowbeast.core.memoryobject import MemoryObject as CoreMO
from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.expr import Expr
from slowbeast.domains.value import Value
from slowbeast.ir.types import get_offset_type, type_mgr
from slowbeast.solvers.symcrete import global_expr_mgr
from slowbeast.util.debugging import dbgv


def write_bytes(values: list, offval, x: Union[Expr, Value]) -> Optional[MemError]:
    """
    Write value "x" at offval + offval + size(x) indices of values list.
    Return None if all is fine or return a MemError object.
    """
    assert values

    if x.type().is_pointer():
        return MemError(MemError.UNSUPPORTED, f"breaking pointer to bytes")

    expr_mgr = global_expr_mgr()
    bw = x.bytewidth()
    # first cast the value to bytes
    ty = type_mgr().bytes_ty(bw)
    x_to_bytes = expr_mgr.BitCast(x, ty)
    if x_to_bytes is None:
        return MemError(MemError.UNSUPPORTED, f"Cast of {x} to {ty} is unsupported")
    xvalues = x_to_bytes.value()
    assert xvalues, values
    if xvalues is None:  # for optimized runs
        return None
    for n, i in enumerate(range(offval, offval + bw)):
        values[i] = xvalues[n]
    return None


def read_bytes(values: list, offval, bts, zeroed):
    assert bts > 0, bts
    assert offval >= 0, offval
    expr_mgr = global_expr_mgr()
    if zeroed:
        c = offval + bts - 1
        # just make Extract return BytesType and it should work well then
        vals = [
            values[c - i] if values[c - i] is not None else ConcreteBitVec(0, 8)
            for i in range(0, bts)
        ]
    else:
        if offval + bts > len(values):
            return None, MemError(
                MemError.UNINIT_READ,
                f"Read of {bts} bytes on offset {offval} "
                f"from object with {len(values)} initialized "
                "values.",
            )
        if any(values[i] is None for i in range(offval, offval + bts)):
            return None, MemError(MemError.UNINIT_READ, "Read of uninitialized byte")
        c = offval + bts - 1
        vals = [values[c - i] for i in range(0, bts)]

    return expr_mgr.bytes(vals), None


def mo_to_bytes(values, size):
    dbgv("Promoting MO to bytes", color="gray")
    assert isinstance(values, dict), values
    newvalues = [None] * size
    for o, val in values.items():
        tmp = write_bytes(newvalues, o, val)
        if tmp is not None:
            return None, tmp
    return newvalues, None


class MemoryObject(CoreMO):
    __slots__ = ()

    def _is_bytes(self):
        return isinstance(self._values, list)

    # FIXME: refactor
    def read(
        self, bts: int, off: Optional[ConcreteVal] = None
    ) -> Union[Tuple[Expr, None], Tuple[ConcreteBitVec, None]]:
        """
        Read 'bts' bytes from offset 'off'. Return (value, None)
        on success otherwise return (None, error)
        """
        assert isinstance(bts, int), "Read non-constant number of bytes"
        if off is None:
            off = ConcreteBitVec(0, get_offset_type())

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

        if self._is_bytes():
            return read_bytes(self._values, offval, bts, self._zeroed)
        return self.read_value(bts, offval, size)

    def read_value(self, bts, offval, size):
        values: dict = self._values
        val = values.get(offval)
        if val is None and self._zeroed:
            if any((values.get(off) for off in range(offval, offval + bts))):
                # there exist some value that overlaps with the range of read bytes
                return self.promote_and_read(bts, offval, size)
            val = ConcreteBitVec(0, 8 * bts)
        if val is None or val.bytewidth() != bts:
            return self.promote_and_read(bts, offval, size)

        # FIXME: make me return BytesType objects (a sequence of bytes)
        return val, None

    def promote_and_read(self, bts, offval, size):
        bytevalues, err = mo_to_bytes(self._values, size)
        if err:
            return None, err
        self._values = bytevalues
        assert isinstance(self._values, list)
        return read_bytes(bytevalues, offval, bts, self._zeroed)

    def write(self, x: Value, off: Optional[ConcreteVal] = None) -> Optional[MemError]:
        """
        Write 'x' to 'off' offset in this object.
        Return None if everything is fine, otherwise return the error
        """
        assert isinstance(x, Value)
        assert self._ro is False, "Writing read-only object (COW bug)"

        if off is None:
            off = ConcreteBitVec(0, get_offset_type())

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
                f"Writing {x.bytewidth()}B to offset {offval} of {size}B object",
            )

        values = self._values
        if self._is_bytes():
            return write_bytes(values, offval, x)
        # does the write overlap? should we promote the object
        # to bytes-object?
        # FIXME: not efficient...
        bw = x.bytewidth()
        for o, val in values.items():
            if offval < o + val.bytewidth() and offval + bw > o:
                if o == offval and val.bytewidth() == bw:
                    break  # the overlap is perfect, we just overwrite the value

                # promote to bytes
                tmp, err = mo_to_bytes(values, size)
                if err:
                    return err
                self._values = tmp
                return write_bytes(tmp, offval, x)

        values[offval] = x
        return None

    def __repr__(self) -> str:
        s = self._repr_header()
        vals = self._values
        for k, v in enumerate(vals) if isinstance(vals, list) else vals.items():
            s += f"\n  {k} -> {v}"
        return s
