from sys import stdout
from .program import ProgramElement


class BBlock(ProgramElement):

    __slots__ = ["_instructions", "_function"]

    def __init__(self, f=None):
        super().__init__()
        self._instructions = []
        self._function = None
        if f:
            f.addBBlock(self)

    def append(self, i):
        i.setBBlock(self, len(self._instructions))
        self._instructions.append(i)

    def insert(self, i, idx):
        assert len(self._instructions) > idx
        # shift indices of the suffix of the bblock
        instrs = self._instructions
        for n in range(idx, len(instrs)):
            instrs[n]._bblock_idx += 1
        instrs.insert(idx, i)
        i.setBBlock(self, idx)

        if __debug__:
            for n, inst in enumerate(self._instructions):
                assert inst.getBBlockIdx() == n, "Invalid insertion of instruction"

    def first(self):
        assert len(self._instructions) > 0
        return self._instructions[0]

    def last(self):
        assert len(self._instructions) > 0
        return self._instructions[-1]

    def empty(self):
        return len(self._instructions) == 0

    def getInstructions(self):
        return self._instructions

    def getInstruction(self, idx):
        assert idx < len(self._instructions)
        return self._instructions[idx]

    def getNextInstruction(self, idx):
        if idx + 1 < len(self._instructions):
            return self._instructions[idx + 1]
        return None

    def setFunction(self, f):
        self._function = f

    def fun(self):
        return self._function

    def as_value(self):
        return "bblock {0}".format(self.getID())

    def size(self):
        return len(self._instructions)

    # def __len__(self):
    #    return len(self._instructions)

    def __iter__(self):
        return self._instructions.__iter__()

    def dump(self, ind=0, stream=stdout, color=True):
        super().dump(ind, stream, color)
        stream.write("{0}; [bblock {1}]\n".format(" " * ind, self.getID()))
        for i in self._instructions:
            i.dump(ind, stream)
