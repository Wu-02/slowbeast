from slowbeast.interpreter.memory import Memory
from slowbeast.ir.value import Constant
from slowbeast.ir.types import Type

#################################
# test 1
#################################
M = Memory()
assert M._objects_ro is False, "Wrongly set RO flag"
N = M.copy()

assert M._objects is N._objects, "References to objects differ"
assert M._objects_ro is True, "Wrongly set RO flag after copy()"
assert N._objects_ro is True, "Wrongly set RO flag after copy()"

M.allocate(4, "dummy")

assert M._objects is not N._objects, "References to objects not changed"
assert M._objects_ro is False, "Wrongly set RO flag after allocate()"
assert N._objects_ro is True, "Wrongly set RO flag after copy()"


#################################
# test 2
#################################
M = Memory()
ptr = M.allocate(Constant(4, Type(32)), "dummy")
assert not M._objects[ptr.getObject().getValue()]._isRO(), "New object is RO"
assert len(M._objects) == 1, "New object not stored in memory"
assert M._objects_ro is False, "Wrongly set RO flag"

N = M.copy()
assert M._objects[ptr.getObject().getValue()]._isRO(), "Object was not made RO"
assert N._objects[ptr.getObject().getValue()]._isRO(), "Object was not made RO"
assert M._objects is N._objects, "References to objects differ"
assert M._objects_ro is True, "Wrongly set RO flag after copy()"
assert N._objects_ro is True, "Wrongly set RO flag after copy()"
assert N.hasObject(ptr.getObject().getValue())
assert M.hasObject(ptr.getObject().getValue())

err = N.write(ptr, Constant(0, Type(32)))
assert not N._objects[ptr.getObject().getValue()]._isRO(), "Object was not properly copied"
assert M._objects[ptr.getObject().getValue()]._isRO(), "Object still should be RO"
assert err is None, "Failed writing to object"
assert M._objects is not N._objects, "References to objects not changed"
assert M._objects_ro is True, "Wrongly set RO flag after write()"
assert N._objects_ro is False, "Wrongly set RO flag after write()"

err = M.write(ptr, Constant(0, Type(32)))
assert not M._objects[ptr.getObject().getValue()]._isRO(), "Object was not properly copied"
assert err is None, "Failed writing to object"
assert M._objects is not N._objects, "References to objects not changed"
assert M._objects_ro is False, "Wrongly set RO flag after write()"
assert N._objects_ro is False, "Wrongly set RO flag after write()"



