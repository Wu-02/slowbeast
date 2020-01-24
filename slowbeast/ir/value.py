#!/usr/bin/python

from . types import Type

POINTER_BYTE_WIDTH = 8

class Value:
    def __init__(self, bw, isptr=False):
        self.type = Type(bw, isptr)

    def getType(self):
        return self.type

    def getByteWidth(self):
        return self.type.getByteWidth()

    def isPointer(self):
        assert not self.type.isPointer()
        return False

    def isConstant(self):
        return False

class Constant(Value):
    def __init__(self, c, bw):
        super(Constant, self).__init__(bw)
        self.value = c

    def asValue(self):
        return "{0}:{1}b".format(str(self.value), self.getByteWidth())

    def getValue(self):
        return self.value

    def isConstant(self):
        return True

    def __str__(self):
        return str(self.value)

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
        assert self.type.isPointer()
        return True

    def dump(self):
        print(self)


