from .programelement import ProgramElement
from slowbeast.ir.types import BitVecType, PointerType
from typing import Optional, Union


class Argument(ProgramElement):
    def __init__(self, ty: Optional[Union[PointerType, BitVecType]]) -> None:
        super().__init__()
        self._type = ty

    def type(self) -> Union[None, BitVecType, PointerType]:
        return self._type

    def __str__(self) -> str:
        return f"a{self.get_id()}:{self._type}"

    def as_value(self) -> str:
        return f"a{self.get_id()}"
