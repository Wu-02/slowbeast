from . program import ProgramElement
from sys import stdout

class BBlock(ProgramElement):

    def __init__(self, f=None):
        super(BBlock, self).__init__()
        self._instructions = []
        self._function = None
        if f:
            f.addBBlock(self)

    def append(self, i):
        i.setBBlock(self, len(self._instructions))
        self._instructions.append(i)

    def empty(self):
        return len(self._instructions) == 0

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

    def dump(self, ind=0, stream=stdout):
        super(BBlock, self).dump(ind,stream)
        stream.write("{0}; [bblock {1}]".format(" "*ind, self.getID()))
        for i in self._instructions:
            i.dump(ind,stream)
