##
# We have three sorts of values:
# boolean
# value with a specified bitwidth
# a pointer to a value (not boolean)


class Type:
    def __init__(self, bw):
        assert isinstance(bw, int)
        self._bitwidth = bw

    def getByteWidth(self):
        return int(max(self._bitwidth / 8, 1))

    def getBitWidth(self):
        return self._bitwidth

    def isPointer(self):
        return False

    def isBool(self):
        return False

    def isArray(self):
        return False

    def __eq__(self, x):
        return self.isBool() == x.isBool() and\
            self.isPointer() == x.isPointer() and\
            self.isArray() == x.isArray() and\
            self.getBitWidth() == x.getBitWidth()

    def __str__(self):
        if self.isBool():
            return 'bool'
        if self.isArray():
            s='array'
        else:
            s=''
        s += '{0}b'.format(self._bitwidth)
        if self.isPointer():
            s += '*'
        return s


# FIXME: make this configurable
POINTER_BIT_WIDTH = 64


class PointerType(Type):
    def __init__(self):
        Type.__init__(self, POINTER_BIT_WIDTH)

    def isPointer(self):
        return True


class BoolType(Type):
    def __init__(self):
        Type.__init__(self, 1)

    def isBool(self):
        return True

class ArrayType(Type):
    """ This corresponds to solver array type, e.g. mapping from int -> bitvec.
        The bitwidth is a bitwidth of one element """
    def __init__(self, bw):
        Type.__init__(self, bw)

    def isArray(self):
        return True


SizeType = Type(POINTER_BIT_WIDTH)
OffsetType = SizeType
