from .program import ProgramElement


class Argument(ProgramElement):
    def __init__(self, ty) -> None:
        super().__init__()
        self._type = ty

    def type(self):
        return self._type

    def __str__(self) -> str:
        return f"a{self.get_id()}:{self._type}"

    def as_value(self) -> str:
        return f"a{self.get_id()}"
