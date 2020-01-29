from . argument import Argument


class Function:
    def __init__(self, name, argNum=0):
        self._name = name
        self._bblocks = []
        self._arguments = [Argument() for x in range(0, argNum)]

    def __eq__(self, other):
        return self._name == other._name

    def isUndefined(self):
        return self._bblocks == []

    def getName(self):
        return self._name

    def getArgument(self, idx):
        assert idx < len(self._arguments)
        return self._arguments[idx]

    def getArguments(self):
        return self._arguments

    def addBBlock(self, bb):
        self._bblocks.append(bb)
        bb.setFunction(self)

    def getBBlock(self, idx):
        assert idx < len(self._bblocks)
        return self._bblocks[idx]

    def dump(self):
        print("fun",
              '{0}({1})'.format(self._name,
                                ', '.join(map(lambda x: x.asValue(),
                                              self._arguments))))

        for b in self._bblocks:
            b.dump(2)
        print("nuf")

    def asValue(self):
        return self._name
