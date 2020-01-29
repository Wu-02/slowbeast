#!/usr/bin/python

from . types import Type, PointerType, BoolType


class Value:
    def __init__(self, ty):
        assert isinstance(ty, Type)
        self._type = ty

    def getType(self):
        return self._type

    def getByteWidth(self):
        return self._type.getByteWidth()

    def getBitWidth(self):
        return self._type.getBitWidth()

    def isPointer(self):
        return self._type.isPointer()

    def isBool(self):
        return self._type.isBool()

    def isConstant(self):
        """
        Is integer constant or boolean constant?
        Overriden by the Constant class
        """
        return False


class Constant(Value):
    """
    Integer constant or boolean
    """

    def __init__(self, c, ty):
        assert isinstance(c, int) or isinstance(c, bool)
        assert isinstance(ty, Type)
        assert not isinstance(c, PointerType)
        super(Constant, self).__init__(ty)
        self._value = c

        assert self.isPointer() == False, "Incorrectly constructed pointer"
        assert not self.isBool() or (c or c == False), "Invalid boolean constant"
        assert self.isBool() or isinstance(c, int)

    def asValue(self):
        return "{0}:{1}".format(str(self._value), self.getType())

    def getValue(self):
        return self._value

    def isConstant(self):
        return True

    def __str__(self):
        return str(self._value)


class Pointer(Value):
    def __init__(self, obj, off=0):
        super(Pointer, self).__init__(PointerType())
        self.object = obj
        self.offset = off

        assert self.isPointer(), "Incorrectly constructed pointer"
        assert self.isBool() == False, "Incorrectly constructed pointer"
        assert self.isConstant() == False, "Incorrectly constructed pointer"

    def __str__(self):
        return "({0}, {1})".format(self.object.asValue(), self.offset)

    def asValue(self):
        return str(self)

    def __eq__(self, oth):
        return self.object == oth.object and self.offset == oth.offset

    def dump(self):
        print(self)
