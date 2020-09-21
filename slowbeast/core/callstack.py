from copy import copy
from sys import stdout


class CallStack:
    class Frame:
        def __init__(self, fun, returnsite=None, v={}):
            self.function = fun
            self.returnsite = returnsite
            self.values = copy(v)
            self._ro = False

        def __eq__(self, rhs):
            return self.function == rhs.function and\
                self.values == rhs.values and\
                self.returnsite == rhs.returnsite

        def _setRO(self):
            self._ro = True

        def _isRO(self):
            return self._ro

        def _cow_reown(self):
            if self._values_ro:
                self.values = copy(self.values)
                self._values_ro = False

        def writableCopy(self):
            new = copy(self)
            new.values = copy(self.values)
            new._ro = False
            return new

        def clear(self):
            self.values = {}

        def set(self, what, v):
            assert self._ro is False, "COW bug"
            self.values[what] = v

        def get(self, v):
            return self.values.get(v)

        def getValuesList(self):
            return self.values.keys()

        def dump(self, stream=stdout):
            for x, v in self.values.items():
                stream.write("{0} -> {1}\n".format(x.asValue(), v.asValue()))

    def __init__(self):
        self._cs = []
        self._cs_ro = False

    def copy(self):
        new = copy(self)
        new._cs_ro = True
        self._cs_ro = True
        for f in self._cs:
            f._setRO()
        return new

    def _cow_reown(self):
        if self._cs_ro:
            assert all([x._isRO() for x in self._cs])
            self._cs = copy(self._cs)
            self._cs_ro = False

    def __eq__(self, rhs):
        return self._cs == rhs._cs

    def frame(self, idx=-1):
        return self._cs[idx]

    def set(self, what, v):
        """ Set a value in the current frame """
        self._cow_reown()
        if self.frame()._isRO():
            self._cs[-1] = self.frame().writableCopy()
            assert not self.frame()._isRO()
        self.frame().set(what, v)

    def get(self, v):
        """ Set a value from the current frame """
        return self.frame().get(v)

    def getValuesList(self, frameidx=-1):
        """ Set a value from the current frame """
        return self.frame(frameidx).getValuesList()

    def pushCall(self, callsite, fun, argsMap):
        self._cow_reown()
        self._cs.append(CallStack.Frame(fun, callsite, argsMap))
        assert not self.frame()._isRO()

    def popCall(self):
        assert len(self._cs) > 0
        self._cow_reown()
        rs = self.frame().returnsite
        del self._cs[-1]
        return rs

    def dump(self, stream=stdout):
        for n, f in enumerate(self._cs):
            stream.write(" -- {0}: {1} --\n".format(n, f.function.getName()))
            f.dump(stream)
