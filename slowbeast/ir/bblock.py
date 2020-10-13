from . program import ProgramElement
from sys import stdout


class BBlock(ProgramElement):

    __slots__ = ['_instructions', '_function']

    def __init__(self, f=None):
        super(BBlock, self).__init__()
        self._instructions = []
        self._function = None
        if f:
            f.addBBlock(self)

    def append(self, i):
        i.setBBlock(self, len(self._instructions))
        self._instructions.append(i)

    def insert(self, i, idx):
        assert len(self._instructions) > idx
        oldi = self._instructions[idx]
        # shift indices of the suffix of the bblock
        for sufi in self._instructions[idx:]:
            sufi._bblock_idx += 1
        self._instructions.insert(idx, i)
        i.setBBlock(self, idx)

        if __debug__:
            for n, i in enumerate(self._instructions):
                assert i._bblock_idx == n, "Invalid insertion of instruction"
                n += 1

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

    def getFunction(self):
        return self._function

    def asValue(self):
        return 'bblock {0}'.format(self.getID())

    def size(self):
        return len(self._instructions)

   # def __len__(self):
   #    return len(self._instructions)

    def __iter__(self):
        return self._instructions.__iter__()

    def dump(self, ind=0, stream=stdout):
        super(BBlock, self).dump(ind, stream)
        stream.write("{0}; [bblock {1}]\n".format(" " * ind, self.getID()))
        for i in self._instructions:
            i.dump(ind, stream)
