from sys import stdout

from .programelement import ProgramElement
from typing import TextIO


class BBlock(ProgramElement):
    __slots__ = ["_instructions", "_function"]

    def __init__(self, f=None) -> None:
        super().__init__()
        self._instructions = []
        self._function = None
        if f:
            f.add_bblock(self)

    def append(self, i) -> None:
        i.set_bblock(self, len(self._instructions))
        self._instructions.append(i)

    def insert(self, i, idx) -> None:
        assert len(self._instructions) > idx
        # shift indices of the suffix of the bblock
        instrs = self._instructions
        for n in range(idx, len(instrs)):
            instrs[n]._bblock_idx += 1
        instrs.insert(idx, i)
        i.set_bblock(self, idx)

        if __debug__:
            for n, inst in enumerate(self._instructions):
                assert inst.bblock_idx() == n, "Invalid insertion of instruction"

    def __getitem__(self, item):
        assert len(self._instructions) > item
        return self._instructions[item]

    def first(self):
        assert len(self._instructions) > 0
        return self._instructions[0]

    def last(self):
        assert len(self._instructions) > 0
        return self._instructions[-1]

    def empty(self) -> bool:
        return len(self._instructions) == 0

    def instructions(self):
        return self._instructions

    def instruction(self, idx):
        assert idx < len(self._instructions)
        return self._instructions[idx]

    def get_next_inst(self, idx):
        if idx + 1 < len(self._instructions):
            return self._instructions[idx + 1]
        return None

    def set_fun(self, f) -> None:
        self._function = f

    def fun(self):
        return self._function

    def as_value(self) -> str:
        return f"bblock {self.get_id()}"

    def size(self) -> int:
        return len(self._instructions)

    # def __len__(self):
    #    return len(self._instructions)

    def __iter__(self):
        return self._instructions.__iter__()

    def dump(self, ind: int = 0, stream: TextIO = stdout, color: bool = True) -> None:
        super().dump(ind, stream, color)
        stream.write(f"{' ' * ind}; [bblock {self.get_id()}]\n")
        for i in self._instructions:
            i.dump(ind, stream)
