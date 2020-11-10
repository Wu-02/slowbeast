#!/usr/bin/python

from .types import Type


class Value:
    __slots__ = ["_type"]

    def __init__(self, ty):
        assert isinstance(ty, Type)
        self._type = ty

    def __eq__(self, other):
        raise NotImplementedError("This must be overriden")

    def type(self):
        return self._type

    def bytewidth(self):
        return self._type.bytewidth()

    def bitwidth(self):
        return self._type.bitwidth()

    def is_pointer(self):
        return self._type.is_pointer()

    def is_bool(self):
        return self._type.is_bool()

    def is_concrete(self):
        """
        Is integer constant or boolean constant?
        Overriden by the ConcreteVal class
        """
        return False


