from . program import ProgramElement

class BBlock(ProgramElement):
    valueCounter = 0

    def __init__(self, f=None):
        super(BBlock, self).__init__()
        BBlock.valueCounter += 1
        self._id = BBlock.valueCounter
        self._instructions = []
        self._function = None
        if f:
            f.addBBlock(self)

    def __eq__(self, rhs):
        return self._id == rhs._id

    def getID(self):
        return self._id

    def append(self, i):
        i.setBasicBlock(self, len(self._instructions))
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

    def dump(self, ind=0):
        super(BBlock, self).dump(ind)
        print(''.join([' ' for x in range(0, ind)]),
              "; [bblock {0}]".format(self.getID()))
        for i in self._instructions:
            i.dump(ind)
