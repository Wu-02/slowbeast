#!/usr/bin/python

from slowbeast.ir.types import Type


class Value:
    __slots__ = "_type"

    def __init__(self, ty: Type) -> None:
        assert isinstance(ty, Type)
        self._type = ty

    def __eq__(self, other: object):
        raise NotImplementedError("This must be overriden")

    def type(self) -> Type:
        return self._type

    def bytewidth(self) -> int:
        return self._type.bytewidth()

    def bitwidth(self):
        return self._type.bitwidth()

    def is_pointer(self) -> bool:
        return self._type.is_pointer()

    def is_bool(self) -> bool:
        return self._type.is_bool()

    def is_int(self) -> bool:
        return self._type.is_int()

    def is_float(self) -> bool:
        return self._type.is_float()

    def is_bytes(self) -> bool:
        return self._type.is_bytes()

    def is_symbolic(self):
        """
        Is integer constant or boolean constant?
        Overriden by the ConcreteVal class
        """
        raise NotImplementedError("Must be overriden")

    def is_concrete(self) -> bool:
        """
        Is this a concrete value? (syntactically)
        """
        return not self.is_symbolic()
