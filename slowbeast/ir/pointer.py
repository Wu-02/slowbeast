from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import IntType, POINTER_BIT_WIDTH, PointerType
from slowbeast.ir.value import Value


class Pointer(Value):

    __slots__ = ["_object", "_offset"]

    def __init__(self, obj,
                 off=ConcreteVal(0, IntType(POINTER_BIT_WIDTH))):
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

    def __eq__(self, oth):
        return self._object == oth._object and self._offset == oth._offset

    def dump(self):
        print(self)