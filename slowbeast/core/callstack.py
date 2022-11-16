from copy import copy
from sys import stdout
from typing import TextIO


class CallStack:
    class Frame:
        __slots__ = (
            "function",
            "returnsite",
            "_values",
            "_scoped_objects",
            "_values_ro",
            "_scoped_objects_ro",
            "_ro",
        )

        def __init__(self, fun, returnsite=None, v=None):
            self.function = fun
            self.returnsite = returnsite
            self._values = v.copy() if v else {}
            self._scoped_objects = []
            self._values_ro = False
            self._scoped_objects_ro = False
            # whole frame is read only
            self._ro = False

        # def __eq__(self, rhs):
        #    return (
        #        self.function == rhs.function
        #        and self.values == rhs.values
        #        and self.returnsite == rhs.returnsite
        #    )

        # def __hash__(self):
        #    r = reduce(xor, map(hash, self.values), 0) ^ hash(self.function)
        #    rets = self.returnsite
        #    return r ^ hash(rets) if rets else r
        def set_ro(self):
            self._ro = True
            self._values_ro = True
            self._scoped_objects_ro = True

        def is_ro(self):
            return self._ro

        def _values_reown(self):
            assert self._ro is False
            if self._values_ro:
                self._values = self._values.copy()
                self._values_ro = False

        def copy(self):
            new = CallStack.Frame(self.function, self.returnsite)
            new._values = self._values
            new._scoped_objects = self._scoped_objects
            new._values_ro = True
            new._scoped_objects_ro = True
            self._values_ro = True
            self._scoped_objects_ro = True
            return new

        def _objects_reown(self):
            assert self._ro is False
            if self._scoped_objects_ro:
                self._scoped_objects = self._scoped_objects.copy()
                self._scoped_objects_ro = False

        def add_scoped_object(self, mo):
            self._objects_reown()
            self._scoped_objects.append(mo)

        def clear(self):
            self._values_ro = False
            self._values = {}
            self._scoped_objects_ro = False
            self._scoped_objects = {}

        def set(self, what, v):
            self._values_reown()
            self._values[what] = v

        def get(self, v):
            return self._values.get(v)

        def values_list(self):
            return self._values.keys()

        def scoped_objects(self):
            return self._scoped_objects

        def dump(self, stream=stdout):
            for x, v in self._values.items():
                stream.write(f"{x.as_value()} -> {v.as_value()}\n")
            stream.write(
                f"scoped objects: {', '.join((f'mo{mo.get_id()}' for mo in self._scoped_objects))}\n"
            )

    def __init__(self) -> None:
        self._cs = []
        self._cs_ro = False

    def copy(self) -> "CallStack":
        new = CallStack()
        new._cs = self._cs
        new._cs_ro = True
        self._cs_ro = True
        for f in self._cs:
            f.set_ro()
        return new

    def _cs_reown(self) -> None:
        if self._cs_ro:
            self._cs = self._cs.copy()
            self._cs_ro = False

    def _frame_reown(self, idx: int = -1) -> None:
        self._cs_reown()
        assert self._cs_ro is False
        frame = self._cs[idx]
        if frame.is_ro():
            self._cs[idx] = frame.copy()

    def __len__(self) -> int:
        return len(self._cs)

    def __iter__(self):
        return self._cs.__iter__()

    def frame(self, idx: int = -1):
        return self._cs[idx]

    def set(self, what, v) -> None:
        """Set a value in the current frame"""
        self._frame_reown()
        self.frame().set(what, v)

    def get(self, v):
        """Set a value from the current frame"""
        return self.frame().get(v)

    def values_list(self, frameidx: int = -1):
        """Set a value from the current frame"""
        return self.frame(frameidx).values_list()

    def push_call(self, callsite, fun, argsMap) -> None:
        self._cs_reown()
        self._cs.append(CallStack.Frame(fun, callsite, argsMap))

    def add_scoped_object(self, mo):
        "Add scoped object to the current frame"
        self._frame_reown()
        return self.frame().add_scoped_object(mo)

    def current_scoped_objects(self):
        return self.frame().scoped_objects()

    def pop_call(self):
        assert len(self._cs) > 0
        self._cs_reown()
        rs = self.frame().returnsite
        del self._cs[-1]
        return rs

    def dump(self, stream: TextIO = stdout) -> None:
        for n, f in enumerate(self._cs):
            name = f.function.name() if f.function else None
            stream.write(f" -- {n}: {name} --\n")
            f.dump(stream)
