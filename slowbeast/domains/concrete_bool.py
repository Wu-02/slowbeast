from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import BoolType


class ConcreteBool(ConcreteVal):
    def __init__(self, b):
        assert isinstance(b, bool), b
        super().__init__(b, BoolType())
