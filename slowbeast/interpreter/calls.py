from copy import copy, deepcopy
from .. util.debugging import dbg


class CallStack:
    class Frame:
        def __init__(self, fun, returnsite=None, v={}):
            self.function = fun
            self.values = copy(v)
            self.returnsite = returnsite

        def __eq__(self, rhs):
            return self.function == rhs.function and\
                self.values == rhs.values and\
                self.returnsite == rhs.returnsite

        def set(self, what, v):
            self.values[what] = v

        def get(self, v):
            return self.values.get(v)

        def dump(self):
            for x, v in self.values.items():
                print(x.asValue(), ' -> ', v.asValue())

    def __init__(self, fun=None, v={}):
        self._cs = []

    def copy(self):
        dbg('FIXME: add COW for CallStack')
        # FIXME: add copy-on-write
        return deepcopy(self)

    def __eq__(self, rhs):
        return self._cs == rhs._cs

    def frame(self, idx=-1):
        return self._cs[idx]

    def set(self, what, v):
        """ Set a value in the current frame """
        self.frame().set(what, v)

    def get(self, v):
        """ Set a value from the current frame """
        return self.frame().get(v)

    def push(self, callsite, fun, argsMap):
        self._cs.append(CallStack.Frame(fun, callsite, argsMap))

    def pop(self):
        assert len(self._cs) > 0
        rs = self.frame().returnsite
        del self._cs[-1]
        return rs

    def dump(self):
        n = 0
        for f in self._cs:
            print(" -- {0}: {1} --".format(n, f.function.getName()))
            f.dump()
            n += 1
