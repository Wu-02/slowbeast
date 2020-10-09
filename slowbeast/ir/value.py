#!/usr/bin/python

from . types import Type, PointerType, BoolType, POINTER_BIT_WIDTH


class Value:
    __slots__ = ['_type']

    def __init__(self, ty):
        assert isinstance(ty, Type)
        self._type = ty

    def __eq__(self, other):
        raise NotImplementedError("This must be overriden")

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

    __slots__ = ['_value']

    def __init__(self, c, ty):
        assert isinstance(c, int) or\
            isinstance(c, bool), f"Invalid constant: {c} {type(c)}"
        assert isinstance(ty, Type), f"Invalid type: {ty}"
        assert not isinstance(ty, PointerType), f"Invalid type: {ty}"
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

    def __hash__(self):
        return self._value

    def __eq__(self, rhs):
        assert isinstance(rhs, Constant)
        return self.getValue() == rhs.getValue() and self.getType() == rhs.getType()


class Pointer(Value):

    __slots__ = ['object', 'offset']

    def __init__(self, obj, off=Constant(0, Type(POINTER_BIT_WIDTH))):
        assert isinstance(off, Value)
        super(Pointer, self).__init__(PointerType())
        self.object = obj
        self.offset = off

        assert self.isPointer(), "Incorrectly constructed pointer"
        assert self.isBool() == False, "Incorrectly constructed pointer"
        assert self.isConstant() == False, "Incorrectly constructed pointer"

    def __str__(self):
        return "({0}, {1})".format(self.object.asValue(), self.offset)

    def getObject(self):
        return self.object

    def getOffset(self):
        return self.offset

    def asValue(self):
        return str(self)

    def __eq__(self, oth):
        return self.object == oth.object and self.offset == oth.offset

    def dump(self):
        print(self)


def ConstantBool(c):
    return Constant(c, BoolType())


ConstantTrue = ConstantBool(True)
ConstantFalse = ConstantBool(False)
