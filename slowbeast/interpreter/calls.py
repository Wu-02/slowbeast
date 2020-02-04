from copy import copy, deepcopy
from .. util.debugging import dbg, FIXME
from sys import stdout


class CallStack:
    class Frame:
        def __init__(self, fun, returnsite=None, v={}):
            self.function = fun
            self.returnsite = returnsite
            self.values = copy(v)
            self._values_ro = False

        def __eq__(self, rhs):
            return self.function == rhs.function and\
                self.values == rhs.values and\
                self.returnsite == rhs.returnsite

        def _cow_reown(self):
            if self._values_ro:
                self.values = copy(self.values)
                self._values_ro = False

        def copy(self):
            new = copy(self)
            self._values_ro = True
            new._values_ro = True
            return new

        def set(self, what, v):
            self._cow_reown()
            self.values[what] = v

        def get(self, v):
            return self.values.get(v)

        def dump(self, stream=stdout):
            for x, v in self.values.items():
                stream.write("{0} -> {1}\n".format(x.asValue(), v.asValue()))

    def __init__(self):
        self._cs = []
        self._cs_ro = False

    def copy(self):
        new = CallStack()
        new._cs = self._cs
        new._cs_ro = True
        self._cs_ro = True
        return new

    def _cow_reown(self):
        # FIXME: We could keep a copy of only
        # the last frame, because we cannot write to other frames
        FIXME("Do better COW on callstack")
        if self._cs_ro:
            tmp = []
            for f in self._cs:
                tmp.append(f.copy())
            self._cs = tmp
            self._cs_ro = False

    def __eq__(self, rhs):
        return self._cs == rhs._cs

    def frame(self, idx=-1):
        return self._cs[idx]

    def set(self, what, v):
        """ Set a value in the current frame """
        self._cow_reown()
        self.frame().set(what, v)

    def get(self, v):
        """ Set a value from the current frame """
        return self.frame().get(v)

    def push(self, callsite, fun, argsMap):
        self._cow_reown()
        self._cs.append(CallStack.Frame(fun, callsite, argsMap))

    def pop(self):
        assert len(self._cs) > 0
        self._cow_reown()
        rs = self.frame().returnsite
        del self._cs[-1]
        return rs

    def dump(self, stream=stdout):
        n = 0
        for f in self._cs:
            stream.write(" -- {0}: {1} --\n".format(n, f.function.getName()))
            f.dump(stream)
            n += 1
