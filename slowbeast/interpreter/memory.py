import sys
from copy import deepcopy

from .. util.debugging import dbg, FIXME
from .. ir.value import *
from .. ir.types import OffsetType

from . memoryobject import MemoryObject
from . errors import ExecutionError


class Memory:
    def __init__(self):
        self._objects = []

    def copy(self):
        FIXME('add COW for memory objects')
        return deepcopy(self)

    def __eq__(self, rhs):
        return self._objects == rhs._objects

    def allocate(self, size, nm=None):
        o = MemoryObject(size, nm)
        self._objects.append(o)
        return Pointer(o)

    def hasObject(self, mo):
        FIXME("Make object lookup efficient")
        for o in self._objects:
            if o == mo:
                return True
        return False

    # def write(self, x, to):
    #     self._vars[to] = x

    # def read(self, frm):
    #     v = self._vars.get(frm)
    #     if v:
    #         return v

    #     raise ExecutionError("Read from uninitialized variable")
    #     return None

    def dump(self, stream=sys.stdout):
        for o in self._objects:
            o.dump(stream)
