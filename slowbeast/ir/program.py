
class Program:
    def __init__(self):
        self._functions = []
        self._entry = None

    def addFun(self, f):
        self._functions.append(f)

    def addGlobal(self, g):
        self._globals.append(g)

    def getFunction(self, name):
        for f in self._functions:
            if f.getName() == name:
                return f
        return None

    def setEntry(self, e):
        assert self.getFunction(e.getName())
        self._entry = e

    def getEntry(self):
        return self._entry

    def dump(self):
        for f in self._functions:
            f.dump()
            print('')


