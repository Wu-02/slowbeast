import sys
from copy import copy

from .. core.callstack import CallStack
from .. ir.value import Pointer, Constant
from .. ir.types import SizeType

from . memoryobject import MemoryObject
from . errors import ExecutionError


class Memory:
    def __init__(self):
        self._objects = {}
        self._objects_ro = False
        self._glob_objects = {}
        self._glob_objects_ro = False
        # callstack containing top-level values for the current
        # function (values of computation of instructions).
        # In the future, move there also the objects bound
        # to particular frames
        self._cs = CallStack()

    def havoc(self):
        self._objects = {}
        self._objects_ro = False
        self._glob_objects = {}
        self._glob_objects_ro = False
        self._cs.havoc()

    def copyTo(self, new):
        new._objects = self._objects
        new._objects_ro = True
        self._objects_ro = True
        new._glob_objects = self._glob_objects
        new._glob_objects_ro = True
        self._glob_objects_ro = True
        for o in self._objects.values():
            o._setRO()
        for o in self._glob_objects.values():
            o._setRO()
        # do not take a reference, but do directly a copy,
        # we'll very probably modify it soon (it's cow internally)
        new._cs = self._cs.copy()
        return new

    def copy(self):
        new = copy(self)
        new._objects_ro = True
        self._objects_ro = True
        new._glob_objects_ro = True
        self._glob_objects_ro = True
        for o in self._objects.values():
            o._setRO()
        for o in self._glob_objects.values():
            o._setRO()
        new._cs = self._cs.copy()
        return new

    def createMO(self, size, nm=None):
        """
        Create a new memory object -- may be overriden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm)

    def _objs_reown(self):
        if self._objects_ro:
            assert all([x._isRO() for x in self._objects.values()])
            self._objects = copy(self._objects)
            self._objects_ro = False

    def _globs_reown(self):
        if self._glob_objects_ro:
            assert all([x._isRO() for x in self._glob_objects.values()])
            self._glob_objects = copy(self._glob_objects)
            self._glob_objects_ro = False

    def __eq__(self, rhs):
        return self._objects == rhs._objects and self._cs == self._cs

    def allocate(self, size, instr=None, nm=None):
        """ Allocate a new memory object and return a pointer to it """
        self._objs_reown()
        o = self.createMO(size, nm)
        assert o._isRO() is False, "Created object is read-only (COW bug)"
        o.setAllocation(instr)
        assert self._objects.get(o.getID()) is None
        self._objects[o.getID()] = o
        return Pointer(Constant(o.getID(), SizeType))

    def allocateGlobal(self, G):
        """ Allocate a new memory object and return a pointer to it """
        self._globs_reown()
        o = self.createMO(G.getSize(), G.getName())
        assert o._isRO() is False, "Created object is read-only (COW bug)"
        o.setAllocation(G)
        assert self._glob_objects.get(o.getID()) is None
        self._glob_objects[o.getID()] = o
        return Pointer(Constant(o.getID(), SizeType))

    def hasGlobalObject(self, moid):
        return self._glob_objects.get(moid) is not None

    def hasObject(self, moid):
        return self._objects.get(
            moid) is not None or self.hasGlobalObject(moid)

    def write(self, ptr, x):
        isglob = False
        obj = self._objects.get(ptr.getObject().getValue())
        if obj is None:
            obj = self._glob_objects.get(ptr.getObject().getValue())
            isglob = True

        if obj is None:
            return None, "Write to invalid object"

        if isglob:
            self._globs_reown()
        else:
            self._objs_reown()

        if obj._isRO():  # copy on write
            obj = obj.writableCopy()
            assert not obj._isRO()
            if isglob:
                self._glob_objects[obj.getID()] = obj
            else:
                self._objects[obj.getID()] = obj

        return obj.write(x, ptr.getOffset())

    def read(self, ptr, bytesNum):
        obj = self._objects.get(ptr.getObject().getValue())
        if obj is None:
            obj = self._glob_objects.get(ptr.getObject().getValue())

        if obj is None:
            return None, "Read from invalid object"

        return obj.read(bytesNum, ptr.getOffset())

    def set(self, what, v):
        self._cs.set(what, v)

    def get(self, v):
        return self._cs.get(v)

    def pushCall(self, callsite, fun, argsMapping={}):
        self._cs.pushCall(callsite, fun, argsMapping)

    def popCall(self):
        return self._cs.popCall()

    def dump(self, stream=sys.stdout):
        for o in self._glob_objects.values():
            o.dump(stream)
        for o in self._objects.values():
            o.dump(stream)
        stream.write("-- Call stack:\n")
        self._cs.dump(stream)