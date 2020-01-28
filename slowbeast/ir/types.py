
class Type:
    def __init__(self, bw, isptr = False):
        self._bitwidth = bw
        self._isptr = isptr

    def getByteWidth(self):
        return int(max(self._bitwidth / 8, 1))

    def getBitWidth(self):
        return self._bitwidth

    def isPointer(self):
        return self._isptr

    def __eq__(self, x):
        return self._bitwidth == _x.bitwidth and self._isptr == x._isptr

    def __str__(self):
        s='{0}b'.format(self._bitwidth)
        if self.isPointer():
            s+='*'
        return s
