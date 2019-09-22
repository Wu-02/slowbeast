
class Function:
    def __init__(self, name):
        self._name = name
        self._bblocks = []

    def getName(self):
        return self._name

    def addBBlock(self, bb):
        self._bblocks.append(bb)
        bb.setFunction(self)

    def getBBlock(self, idx):
        assert idx < len(self._bblocks)
        return self._bblocks[idx]

    def dump(self):
        print("fun", self._name)
        for b in self._bblocks:
            b.dump(2)
            print('')
        print("nuf")
