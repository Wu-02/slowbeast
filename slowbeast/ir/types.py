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


def get_size_type() -> "BitVecType":
    return BitVecType(POINTER_BIT_WIDTH)


def get_offset_type() -> "BitVecType":
    return BitVecType(POINTER_BIT_WIDTH)


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

    def bitwidth(self) -> int:
        return self._bitwidth

    def is_pointer(self) -> bool:
        return False

    def is_bv(self) -> bool:
        return False

    def is_float(self) -> bool:
        return False

    def is_bytes(self) -> bool:
        """Uninterpreted sequence of bytes"""
        return False

    def is_bool(self) -> bool:
        return False

    def is_label(self) -> bool:
        return False

    def __eq__(self, other: object):
        # FIXME: do this better
        return isinstance(other, Type) and str(self) == str(other)

    def __str__(self: "Type") -> str:
        s = ""
        if self.is_bool():
            s = "bool"
        elif self.is_float():
            s = f"f{self.bitwidth()}b"
        elif self.is_bytes():
            s = f"[i8; {self.bytewidth()}]"
        elif self.is_bv():
            s = f"{self.bitwidth()}b"
        elif self.is_label():
            s = "addr"
        else:
            assert self.is_pointer(), f"Invalid type: {type(self)}"

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


class BitVecType(Type):
    def __init__(self, bw: int) -> None:
        Type.__init__(self, bw)

    def is_bv(self) -> bool:
        return True


class FloatType(Type):
    def __init__(self, bw: int) -> None:
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


class LabelType(PointerType):
    """
    Pointer pointing somewhere to the code (usually a basic block pointer)
    """

    def is_label(self) -> bool:
        return True
