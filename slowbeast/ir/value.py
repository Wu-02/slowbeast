#!/usr/bin/python

from . types import Type

POINTER_BYTE_WIDTH = 8

class Value:
    def __init__(self, bw, isptr=False):
        self._type = Type(bw, isptr)

    def getType(self):
        return self._type

    def getByteWidth(self):
        return self._type.getByteWidth()

    def getBitWidth(self):
        return self._type.getBitWidth()

    def isPointer(self):
        assert not self._type.isPointer()
        return False

    def isConstant(self):
        return False

class Constant(Value):
    def __init__(self, c, bw):
        super(Constant, self).__init__(bw)
        self._value = c

    def asValue(self):
        return "{0}:{1}b".format(str(self._value), self.getBitWidth())

    def getValue(self):
        return self._value

    def isConstant(self):
        return True

    def __str__(self):
        return str(self._value)

class Pointer(Value):
    def __init__(self, obj, off = 0):
        super(Pointer, self).__init__(POINTER_BYTE_WIDTH, isptr=True)
        self.object = obj
        self.offset = off

    def __str__(self):
        return "({0}, {1})".format(self.object.asValue(), self.offset)

    def asValue(self):
        return str(self)

    def __eq__(self, oth):
        return self.object == oth.object and self.offset == oth.offset

    def isPointer(self):
        assert self.getType().isPointer()
        return True

    def dump(self):
        print(self)


