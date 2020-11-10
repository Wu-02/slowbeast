#!/usr/bin/python

from .types import IntType, Type, PointerType, BoolType, POINTER_BIT_WIDTH

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

class ConcreteVal(Value):
    """
    Integer constant or boolean
    """

    __slots__ = ["_value"]

    def __init__(self, c, ty):
        assert isinstance(c, (int, bool)), f"Invalid constant: {c} {type(c)}"
        assert isinstance(ty, Type), f"Invalid type: {ty}"
        assert not isinstance(ty, PointerType), f"Invalid type: {ty}"
        super().__init__(ty)
        self._value = c

        assert not self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool() or (c in (True, False)), "Invalid boolean constant"
        assert self.is_bool() or isinstance(c, int)

    def as_value(self):
        return "{0}:{1}".format(str(self._value), self.type())

    def value(self):
        return self._value

    def is_concrete(self):
        return True

    def __repr__(self):
        return f"{self._value}:{self.type()}"

    def __hash__(self):
        return self._value

    def __eq__(self, rhs):
        assert isinstance(rhs, ConcreteVal)
        return self.value() == rhs.value() and self.type() == rhs.type()


class Pointer(Value):

    __slots__ = ["_object", "_offset"]

    def __init__(self, obj,
                 off=ConcreteVal(0, IntType(POINTER_BIT_WIDTH))):
        assert isinstance(off, Value)
        super().__init__(PointerType())
        self._object = obj
        self._offset = off

        assert self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool(), "Incorrectly constructed pointer"
        assert not self.is_concrete(), "Incorrectly constructed pointer"

    def __str__(self):
        return "({0}, {1})".format(self._object.as_value(), self._offset)

    def object(self):
        return self._object

    def offset(self):
        return self._offset

    def as_value(self):
        return str(self)

    def __eq__(self, oth):
        return self._object == oth._object and self._offset == oth._offset

    def dump(self):
        print(self)


def ConstantBool(c):
    return ConcreteVal(c, BoolType())


ConstantTrue = ConstantBool(True)
ConstantFalse = ConstantBool(False)
