from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import POINTER_BIT_WIDTH, PointerType
from slowbeast.domains.value import Value


class Pointer(Value):

    __slots__ = "_object", "_offset"

    def __init__(self, obj, off=ConcreteInt(0, POINTER_BIT_WIDTH)):
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

    def is_concrete(self):
        return False

    def __eq__(self, oth):
        return self._object == oth._object and self._offset == oth._offset

    def __hash__(self, oth):
        return hash(self._object) ^ hash(self._offset)

    def dump(self):
        print(self)
