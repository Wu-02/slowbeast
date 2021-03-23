from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import POINTER_BIT_WIDTH, PointerType
from slowbeast.domains.value import Value


class Pointer(Value):

    __slots__ = "_object", "_offset"
    KIND = 5

    def __init__(self, obj, off=ConcreteInt(0, POINTER_BIT_WIDTH)):
        assert isinstance(obj, Value)
        assert isinstance(off, Value)
        super().__init__(PointerType())
        self._object = obj
        self._offset = off

        assert self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool(), "Incorrectly constructed pointer"

    def __repr__(self):
        return "ptr({0}, {1})".format(self._object.as_value(), self._offset)

    def object(self):
        return self._object

    def offset(self):
        return self._offset

    def as_value(self):
        return str(self)

    def is_concrete(self):
        return self._object.is_concrete() and self._offset.is_concrete()

    def is_null(self):
        return self.is_concrete() and self._object.is_zero() and self._offset.is_zero()

    def symbols(self):
        yield from self._object.symbols()
        yield from self._offset.symbols()

    def __eq__(self, oth):
        return self._object == oth._object and self._offset == oth._offset

    def __hash__(self):
        return (hash(self._object) & 0xffffff) ^ ((hash(self._offset) << 32) & 0xffffffff00000000)

    def dump(self):
        print(self)


NullPointer = Pointer(
    ConcreteInt(0, POINTER_BIT_WIDTH), ConcreteInt(0, POINTER_BIT_WIDTH)
)
