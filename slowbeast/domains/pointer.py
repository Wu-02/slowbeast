from .concrete_bitvec import ConcreteBitVec
from slowbeast.domains.value import Value
from slowbeast.ir.types import get_offset_type_size, PointerType
from . import POINTER_KIND
from typing import Optional


class Pointer(Value):
    __slots__ = "_object", "_offset"
    KIND = POINTER_KIND

    def __init__(self, obj: Value, off: Optional[Value] = None) -> None:
        assert isinstance(obj, Value)
        assert off is None or isinstance(off, Value)
        super().__init__(None, PointerType())
        # value is used for the address the pointer points to -- we use that only
        # if that is a symbolic address, so it is usually None
        self._object = obj
        self._offset = off or ConcreteBitVec(0, get_offset_type_size())

        assert self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool(), "Incorrectly constructed pointer"

    def __repr__(self) -> str:
        s = f"ptr({self._object.as_value()}, {self._offset})"
        if self._value:
            return f"{s}[{self._value}]"
        return s

    def object(self) -> Value:
        return self._object

    def offset(self):
        return self._offset

    def as_value(self) -> str:
        return str(self)

    def is_concrete(self):
        return self._object.is_concrete() and self._offset.is_concrete()

    def is_null(self):
        return self.is_concrete() and self._object.is_zero() and self._offset.is_zero()

    # FIXME: make a function for this...
    def symbols(self):
        yield from self._object.symbols()
        yield from self._offset.symbols()

    def __eq__(self, oth):
        return self._object == oth._object and self._offset == oth._offset

    def __hash__(self) -> int:
        return (hash(self._object) & 0xFFFFFF) ^ (
            (hash(self._offset) << 32) & 0xFFFFFFFF00000000
        )

    def dump(self) -> None:
        print(self)


def get_null_pointer() -> Pointer:
    return Pointer(
        ConcreteBitVec(0, get_offset_type_size()),
        ConcreteBitVec(0, get_offset_type_size()),
    )
