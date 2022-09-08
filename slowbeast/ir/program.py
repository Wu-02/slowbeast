from sys import stdout
from typing import TextIO, List, Dict, Optional

from . function import Function
from . instruction import GlobalVariable


class Program:
    __slots__ = "_functions", "_entry", "_metadata", "_globals"

    def __init__(self) -> None:
        self._functions: List[Function] = []
        self._entry: Optional[Function] = None
        self._metadata: Dict[str, object] = {}
        self._globals: List[GlobalVariable] = []

    def add_fun(self, f: Function) -> None:
        self._functions.append(f)

    def funs(self) -> List[Function]:
        return self._functions

    def fun(self, name: str):
        for f in self._functions:
            if f.name() == name:
                return f
        return None

    def set_entry(self, e: Function) -> None:
        assert self.fun(e.name())
        self._entry = e

    def entry(self) -> Function:
        assert self._entry is not None
        return self._entry

    def add_global(self, g: GlobalVariable) -> None:
        self._globals.append(g)

    def globals(self) -> List[GlobalVariable]:
        return self._globals

    def __iter__(self):
        return self._functions.__iter__()

    def dump(self, stream: TextIO = stdout) -> None:
        for g in self._globals:
            g.dump(stream=stream)
            stream.write("\n")
        for f in self._functions:
            f.dump(stream=stream)
            stream.write("\n")
