from sys import stdout
from slowbeast.util.debugging import print_stream


class Program:

    __slots__ = ["_functions", "_entry", "_metadata", "_globals"]

    def __init__(self):
        self._functions = []
        self._entry = None
        self._metadata = {}
        self._globals = []

    def addFun(self, f):
        self._functions.append(f)

    def funs(self):
        return self._functions

    def fun(self, name):
        for f in self._functions:
            if f.getName() == name:
                return f
        return None

    def setEntry(self, e):
        assert self.fun(e.getName())
        self._entry = e

    def getEntry(self):
        return self._entry

    def addGlobal(self, g):
        self._globals.append(g)

    def getGlobals(self):
        return self._globals

    def __iter__(self):
        return self._functions.__iter__()

    def dump(self, stream=stdout):
        for g in self._globals:
            g.dump(stream=stream)
            stream.write("\n")
        for f in self._functions:
            f.dump(stream=stream)
            stream.write("\n")


class ProgramElement:
    """
    Basic class for all elements of a program (functions, instructions, global values,
    basic blocks). Just anything to which we want to assign any metadata.
    """

    elemsCounter = 0

    __slots__ = ["_metadata", "_id"]

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

    def isGlobal(self):
        """ Is visible everywhere in the program? """
        return False

    def getID(self):
        return self._id

    def __eq__(self, rhs):
        return self._id == rhs._id

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._id

    def dump(self, ind=0, stream=stdout, color=True):
        col = "GRAY" if color else "BLACK"
        for k, v in self._metadata:
            print_stream(
                "{0} ; {1} : {2}".format(" " * ind, k, v), color=col, stream=stream
            )
