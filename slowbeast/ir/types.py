##
# We have five sorts of values:
# boolean
# value with a specified bitwidth
# floating-point value
# a sequence of bytes
# and a pointer to a value (not boolean)

POINTER_BIT_WIDTH = 64


def get_pointer_bitwidth() -> int:
    return POINTER_BIT_WIDTH


def get_size_type() -> "IntType":
    return IntType(POINTER_BIT_WIDTH)


def get_offset_type() -> "IntType":
    return IntType(POINTER_BIT_WIDTH)


def get_size_type_size() -> int:
    return POINTER_BIT_WIDTH


def get_offset_type_size() -> int:
    return POINTER_BIT_WIDTH


def sb_set_pointer_width(width: int) -> None:
    global POINTER_BIT_WIDTH
    assert width % 8 == 0
    POINTER_BIT_WIDTH = width
    # we must reset the types that use POINTER_BIT_WIDTH


class Type:
    __slots__ = "_bitwidth"

    def __init__(self, bw: int) -> None:
        assert isinstance(bw, int)
        self._bitwidth = bw

    def bytewidth(self) -> int:
        return max(int(self._bitwidth / 8), 1)

    def bitwidth(self):
        return self._bitwidth

    def is_pointer(self) -> bool:
        return False

    def is_int(self) -> bool:
        return False

    def is_float(self) -> bool:
        return False

    def is_bytes(self) -> bool:
        """Uninterpreted sequence of bytes"""
        return False

    def is_bool(self) -> bool:
        return False

    def __eq__(self, x: object):

        return (
            self.is_bool() == x.is_bool()
            and self.is_pointer() == x.is_pointer()
            and self.is_float() == x.is_float()
            and self.bitwidth() == x.bitwidth()
        )

    def __str__(self) -> str:
        if self.is_bool():
            return "bool"
        if self.is_float():
            s = f"f{self._bitwidth}b"
        elif self.is_bytes():
            s = f"x{self._bitwidth}"
        else:
            s = f"{self._bitwidth}b"
        if self.is_pointer():
            s += "*"
        return s


#  FIXME: add type manager that will manage the types,
#  mainly, we will not create a new object for every value,
#  but the types will be shared (and thus we can also modify them
#  easily)


class PointerType(Type):
    def __init__(self) -> None:
        Type.__init__(self, get_pointer_bitwidth())

    def is_pointer(self) -> bool:
        return True


class IntType(Type):
    def __init__(self, bw) -> None:
        Type.__init__(self, bw)

    def is_int(self) -> bool:
        return True


class FloatType(Type):
    def __init__(self, bw) -> None:
        Type.__init__(self, bw)

    def is_float(self) -> bool:
        return True


class BoolType(Type):
    def __init__(self) -> None:
        Type.__init__(self, 1)

    def is_bool(self) -> bool:
        return True


class Bytes(Type):
    def __init__(self, bytenum) -> None:
        Type.__init__(self, bytenum * 8)

    def is_bytes(self) -> bool:
        return True
