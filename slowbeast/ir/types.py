
class Type:
    def __init__(self, bw, isptr = False):
        self.bytewidth = bw
        self.isptr = isptr

    def getByteWidth(self):
        return self.bytewidth

    def isPointer(self):
        return self.isptr

    def __str__(self):
        s='{0}B'
        if self.isPointer():
            s+='*'
        return s
