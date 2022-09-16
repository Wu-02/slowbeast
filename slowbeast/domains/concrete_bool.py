from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import BoolType


class ConcreteBool(ConcreteVal):
    def __init__(self, b: bool) -> None:
        assert isinstance(b, bool), f"{b} type: {type(b)}"
        super().__init__(b, BoolType())
