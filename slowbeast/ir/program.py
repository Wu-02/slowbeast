from .. util.debugging import print_stream
from sys import stdout

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

    def dump(self, stream=stdout):
        for f in self._functions:
            f.dump(stream)
            stream.write('\n')


class ProgramElement:
    """
    Basic class for all elements of a program (functions, instructions, global values,
    basic blocks). Just anything to which we want to assign any metadata.
    """

    elemsCounter = 0

    def __init__(self):
        """
        Metadata is a list of tuples (key, data).
        The key is not unique (therefore its a list).
        """
        self._metadata = []

        ProgramElement.elemsCounter += 1
        self._id = ProgramElement.elemsCounter

    def getMetadata(self):
        return self._metadata

    def addMetadata(self, key, value):
        assert isinstance(key, str)
        self._metadata.append((key, value))

    def getID(self):
        return self._id

    def __eq__(self, rhs):
        return self._id == rhs._id

    def __ne__(self, other):
        return not(self.__eq__(self, other))

    def __hash__(self):
        return self._id

    def dump(self, ind=0, stream=stdout):
        for k, v in self._metadata:
            print_stream(stream,
                         "{0} ; {1} : {2}".format(
                         ''.join([' ' for x in range(0, ind)]),
                         k, v), color="GRAY")
