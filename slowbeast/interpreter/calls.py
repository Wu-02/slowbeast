
class CallStack:
    class Frame:
        def __init__(self, fun, returnsite = None, v = {}):
            self.function = fun
            self.values = v
            self.returnsite = returnsite

        def set(self, what, v):
            self.values[what] = v

        def get(self, v):
            return self.values.get(v)

        def dump(self):
            for x, v in self.values.items():
                print(x.asValue(), ' -> ', v.asValue())


    def __init__(self, fun = None, v = {}):
        self._cs = [CallStack.Frame(fun, None, v)]

    def frame(self, idx = -1):
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
            print(" -- {0}: {1} --".format(n, f.function))
            f.dump()
            n += 1

