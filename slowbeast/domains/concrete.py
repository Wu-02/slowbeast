from slowbeast.domains import CONCRETE_DOMAIN_KIND
from slowbeast.domains.value import Value
from slowbeast.ir.types import Type, PointerType


class ConcreteVal(Value):
    """
    Integer constant or boolean
    """

    KIND = CONCRETE_DOMAIN_KIND

    def __init__(self, c, ty):
        assert isinstance(c, (int, bool, float)), f"Invalid constant: {c} {type(c)}"
        assert isinstance(ty, Type), f"Invalid type: {ty}"
        assert not isinstance(ty, PointerType), f"Invalid type: {ty}"
        super().__init__(c, ty)

        assert not self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool() or (c in (True, False)), "Invalid boolean constant"
        assert self.is_bool() or isinstance(c, (int, float))

    def as_value(self):
        return f"{str(self._value)}:{self.type()}"

    def value(self):
        return self._value

    def is_concrete(self):
        return True

    def is_symbolic(self):
        return False

    def symbols(self):
        return ()

    def is_zero(self):
        return self._value == 0

    def is_one(self):
        return self._value == 1

    def __repr__(self):
        return f"{self._value}:{self.type()}"

    def __hash__(self):
        return self._value

    def __eq__(self, rhs):
        return (
            False
            if not isinstance(rhs, ConcreteVal)
            else self.value() == rhs.value() and self.type() == rhs.type()
        )
