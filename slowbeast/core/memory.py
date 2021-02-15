import sys
from copy import copy

from slowbeast.core.callstack import CallStack
from slowbeast.core.errors import MemError
from slowbeast.domains.pointer import Pointer
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import SizeType

from .memoryobject import MemoryObject


class Memory:
    """
    This is the object that keeps track of the state of memory
    in an execution state. It is created by MemoryModel object
    which also handles its updates and queries.
    """

    def __init__(self):
        self._objects = {}
        self._objects_ro = False
        self._glob_objects = {}
        self._glob_objects_ro = False
        self._glob_bindings = {}
        self._glob_bindings_ro = False
        # callstack containing top-level values for the current
        # function (values of computation of instructions).
        # In the future, move there also the objects bound
        # to particular frames
        self._cs = CallStack()

    def copyTo(self, new):
        new._objects = self._objects
        new._objects_ro = True
        self._objects_ro = True
        new._glob_objects = self._glob_objects
        new._glob_objects_ro = True
        self._glob_objects_ro = True
        new._glob_bindings = self._glob_bindings
        new._glob_bindings_ro = True
        self._glob_bindings_ro = True
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
        new._glob_bindings_ro = True
        self._glob_bindings_ro = True
        for o in self._objects.values():
            o._setRO()
        for o in self._glob_objects.values():
            o._setRO()
        new._cs = self._cs.copy()
        return new

    def createMO(self, size, nm=None, objid=None):
        """
        Create a new memory object -- may be overriden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid)

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

    def _globs_bindings_reown(self):
        if self._glob_bindings_ro:
            self._glob_bindings = copy(self._glob_bindings)
            self._glob_bindings_ro = False

    def __eq__(self, rhs):
        return self._objects == rhs._objects and self._cs == self._cs

    def _allocate(self, size, instr=None, nm=None, objid=None):
        """ Allocate a new memory object and return it """
        o = self.createMO(size, nm, objid)
        assert o._isRO() is False, "Created object is read-only (COW bug)"

        if instr:
            o.setAllocation(instr)

        return o

    def allocate(self, size, instr=None, nm=None, objid=None):
        """ Allocate a new memory object and return a pointer to it """
        assert (
            objid is None or self._objects.get(objid) is None
        ), "Already has an object with id {0}".format(objid)

        o = self._allocate(size, instr, nm, objid)

        self._objs_reown()
        assert self._objects.get(o.get_id()) is None
        self._objects[o.get_id()] = o

        return Pointer(ConcreteVal(o.get_id(), SizeType))

    def allocateGlobal(self, G, objid=None):
        """ Allocate a new memory object and return a pointer to it """
        assert (
            objid is None or self._glob_objects.get(objid) is None
        ), "Already has a global object with id {0}".format(objid)

        o = self._allocate(G.size(), G, G.name(), objid)

        self._globs_reown()
        assert self._glob_objects.get(o.get_id()) is None
        self._glob_objects[o.get_id()] = o

        self._globs_bindings_reown()
        assert self._glob_bindings_ro is False
        assert self._glob_bindings.get(G) is None
        ptr = Pointer(ConcreteVal(o.get_id(), SizeType))
        self._glob_bindings[G] = ptr

        return ptr

    def hasGlobalObject(self, moid):
        return self._glob_objects.get(moid) is not None

    def hasObject(self, moid):
        return self._objects.get(moid) is not None or self.hasGlobalObject(moid)

    def get_obj(self, moid):
        if isinstance(moid, ConcreteVal):
            moid = moid.value()
        assert isinstance(moid, int), f"Invalid MO ID: {moid}"
        obj = self._objects.get(moid)
        if obj is None:
            return self._glob_objects.get(moid)
        return obj

    def write(self, ptr, x):
        isglob = False
        objid = ptr.object().value()
        obj = self._objects.get(objid)
        if obj is None:
            obj = self._glob_objects.get(objid)
            isglob = True

        if obj is None:
            return None, MemError(MemError.INVALID_OBJ, str(ptr.object()))

        if isglob:
            self._globs_reown()
        else:
            self._objs_reown()

        if obj._isRO():  # copy on write
            obj = obj.writableCopy()
            assert not obj._isRO()
            if isglob:
                self._glob_objects[obj.get_id()] = obj
            else:
                self._objects[obj.get_id()] = obj

        return obj.write(x, ptr.offset())

    def read(self, ptr, bytesNum):
        obj = self._objects.get(ptr.object().value())
        if obj is None:
            obj = self._glob_objects.get(ptr.object().value())

        if obj is None:
            return None, MemError(MemError.INVALID_OBJ, str(ptr.object()))

        return obj.read(bytesNum, ptr.offset())

    def set(self, what, v):
        self._cs.set(what, v)

    def get(self, v):
        ret = self._glob_bindings.get(v)
        if ret is None:
            ret = self._cs.get(v)
        return ret

    def globalsList(self):
        """ Return the list of globals in this state """
        # return only list, so that we must get them through "get"
        return self._glob_bindings.keys()

    def getValuesList(self):
        return self._cs.getValuesList()

    def pushCall(self, callsite, fun, argsMapping={}):
        self._cs.pushCall(callsite, fun, argsMapping)

    def popCall(self):
        return self._cs.popCall()

    def dump(self, stream=sys.stdout):
        stream.write("-- Global objects:\n")
        for o in self._glob_objects.values():
            o.dump(stream)
        stream.write("-- Global bindings:\n")
        for g, v in self._glob_bindings.items():
            stream.write("{0} -> {1}\n".format(g.as_value(), v.as_value()))
        stream.write("-- Objects:\n")
        for o in self._objects.values():
            o.dump(stream)
        stream.write("-- Call stack:\n")
        self._cs.dump(stream)


    def havoc_obj(self, objid):
        isglob = False
        obj = self._objects.get(objid)
        if obj is None:
            obj = self._glob_objects.get(objid)
            isglob = True

        if obj is None:
            return

        if isglob:
            self._globs_reown()
        else:
            self._objs_reown()

        if obj._isRO():
            obj = obj.clean_copy()
            assert not obj._isRO()
            if isglob:
                self._glob_objects[obj.get_id()] = obj
            else:
                self._objects[obj.get_id()] = obj
        else:
            obj.clear()


    def havoc(self, objs=None):
        """ Havoc the contents of memory """
        # FIXME: we do not have to havoc constants and some other values
        if objs:
            havoc_obj = self.havoc_obj
            for o in objs:
                havoc_obj(o.get_id())
            return

        raise NotImplementedError("Havocing all memory unsupported yet")
       #newobjs = {}
       #self._objects_ro = False
       #createMO = self.createMO()
       #for p, o in self._objects.items():
       #    no = createMO(o.size(), o.name(), o.get_id())
       #    no.setAllocation(no.allocation())
       #    newobjs[p] = no




