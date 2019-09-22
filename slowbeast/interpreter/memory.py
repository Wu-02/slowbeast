from . errors import ExecutionError

class Pointer:
    def __init__(self, obj, off = 0):
        self.object = obj
        self.offset = off

    def __str__(self):
        return "({0}, {1})".format(self.object.asValue(), self.offset)

    def asValue(self):
        return str(self)

    def __eq__(self, oth):
        return self.object == oth.object and self.offset == oth.offset

    def dump(self):
        print(self)

class MemoryObject:
    ids = 0

    def __init__(self, size, nm = "unnamed"):
        MemoryObject.ids += 1
        self._id = MemoryObject.ids

        self.value = None # until we support composite objects, use just 'value'
        self.size = size
        self.name = nm # for debugging
        self.allocation = None # which allocation allocated this memory

    def setAllocation(self, a):
        self.allocation = a

    def write(self, x, off = 0):
        assert off == 0 # not implemented otherwise
        self.value = x

    def read(self, off = 0):
        assert off == 0 # not implemented otherwise
        if self.value is None:
            raise ExecutionError("Read from uninitialized variable")
        return self.value

    def __str__(self):
        if hasattr(self.value, 'asValue'):
            v = self.value.asValue()
        else:
            v = self.value
        return "mo{0} ({1} alloc. by {2}), {3}b -> {4}".format(self._id, self.name,
                                                               self.allocation.asValue() if self.allocation else "unknown",
                                                               self.size, v)

    def asValue(self):
        return "mo{0}".format(self._id)

    def dump(self):
        print(str(self))

class Memory:
    def __init__(self):
        self._objects = []

    def allocate(self, size, nm = None):
        o = MemoryObject(size, nm)
        self._objects.append(o)
        return Pointer(o, 0)

    # def write(self, x, to):
    #     self._vars[to] = x

    # def read(self, frm):
    #     v = self._vars.get(frm)
    #     if v:
    #         return v

    #     raise ExecutionError("Read from uninitialized variable")
    #     return None

    def dump(self):
        for o in self._objects:
            o.dump()
