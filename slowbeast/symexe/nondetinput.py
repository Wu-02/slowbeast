class NondetInput:
    __slots__ = "instruction", "value"

    def __init__(self, instr, val) -> None:
        self.instruction = instr
        self.value = val

    def is_nondet_call(self) -> bool:
        return False

    def is_nondet_load(self) -> bool:
        return False

    def is_nondet_instr(self) -> bool:
        return True

    def __repr__(self) -> str:
        return f"{self.instruction.as_value()} = {self.value}"
