
class Program:
    def __init__(self):
        self._functions = []
        self._entry = None
        self._metadata = {}

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

class ProgramElement:
    """
    Basic class for all elements of a program (functions, instructions, global values,
    basic blocks). Just anything to which we want to assign any metadata.
    """
    def __init__(self):
        """
        Metadata is a list of tuples (key, data).
        The key is not unique (therefore its a list).
        """
        self._metadata = []
        # XXX: do we want a unique ID to each program element?

    def getMetadata(self):
        return self._metadata

    def addMetadata(self, key, value):
        assert isinstance(key, str)
        self._metadata.append((key, value))

    def dump(self, ind = 0):
        for k, v in self._metadata:
            print("{0} ; {1} : {2}".format(
                  ''.join([' ' for x in range(0, ind)]),
                  k, v))
