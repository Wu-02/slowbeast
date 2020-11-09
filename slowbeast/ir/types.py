##
# We have three sorts of values:
# boolean
# value with a specified bitwidth
# a pointer to a value (not boolean)


class Type:
    __slots__ = ["_bitwidth"]

    def __init__(self, bw):
        assert isinstance(bw, int)
        self._bitwidth = bw

    def bytewidth(self):
        return int(max(self._bitwidth / 8, 1))

    def bitwidth(self):
        return self._bitwidth

    def is_pointer(self):
        return False

    def is_bool(self):
        return False

    def __eq__(self, x):

        return (
            self.is_bool() == x.is_bool()
            and self.is_pointer() == x.is_pointer()
            and self.bitwidth() == x.bitwidth()
        )

    def __str__(self):
        if self.is_bool():
            return "bool"
        s = "{0}b".format(self._bitwidth)
        if self.is_pointer():
            s += "*"
        return s


POINTER_BIT_WIDTH = 64


def sb_set_pointer_width(width):
    global POINTER_BIT_WIDTH
    assert width % 8 == 0
    POINTER_BIT_WIDTH = 64


class PointerType(Type):
    def __init__(self):
        Type.__init__(self, POINTER_BIT_WIDTH)

    def is_pointer(self):
        return True


class BoolType(Type):
    def __init__(self):
        Type.__init__(self, 1)

    def is_bool(self):
        return True


SizeType = Type(POINTER_BIT_WIDTH)
OffsetType = SizeType
