from slowbeast.domains.value import Value
from slowbeast.ir.types import type_mgr


class SymbolicBytes(Value):
    """
    A sequence of concrete bitvectors of length 8.
    """

    def __init__(self, values: list) -> None:
        assert isinstance(values, list), values
        assert all((a.bitwidth() == 8 for a in values)), values
        assert all((isinstance(a, Value) for a in values)), values
        ty = type_mgr().bytes_ty(len(values))
        super().__init__(values, ty)
