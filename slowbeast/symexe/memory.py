from copy import copy
from ..util.debugging import dbgv
from ..core.memory import Memory
from ..core.memoryobject import MemoryObject
from ..core.memorymodel import MemoryModel
from ..ir.types import OffsetType
from ..ir.value import Constant, Value
from ..ir.instruction import Alloc, GlobalVariable, Load

from slowbeast.domains.symbolic import NondetLoad


class SymbolicMemoryModel(MemoryModel):

    __slots__ = ["solver"]

    def __init__(self, opts, solver):
        super(SymbolicMemoryModel, self).__init__(opts)
        assert solver is not None
        self.solver = solver

    def getSolver(self):
        return self.solver


# def createMemory(self):
#    return SymbolicMemory(self.solver)


class LazySymbolicMemoryModel(SymbolicMemoryModel):
    def __init__(self, opts, solver):
        super(LazySymbolicMemoryModel, self).__init__(opts, solver)

    def lazyAllocate(self, state, op):
        assert isinstance(op, Alloc) or isinstance(op, GlobalVariable)
        s = self.allocate(state, op)
        assert len(s) == 1 and s[0] is state
        dbgv("Lazily allocated {0}".format(op), color="WHITE")
        assert state.get(op), "Did not bind an allocated value"

    def write(self, state, valueOp, toOp):
        value = state.eval(valueOp)
        to = state.get(toOp)
        if to is None:
            self.lazyAllocate(state, toOp)
            # FIXME "We're calling get() method but we could return the value..."
            to = state.get(toOp)

        assert isinstance(value, Value)
        assert to.is_pointer()
        if not to.getOffset().is_concrete():
            # FIXME: move this check to memory.write() object
            state.setKilled("Write with non-constant offset not supported yet")
            return [state]
        try:
            err = state.memory.write(to, value)
        except NotImplementedError as e:
            state.setKilled(str(e))
            return [state]
        if err:
            state.setError(err)
        return [state]

    def uninitializedRead(self, state, frm, ptr, bytesNum):
        dbgv("Reading nondet for uninitialized value: {0}".format(ptr), color="WHITE")
        # NOTE: this name identifier is reserved for value representing
        # uninitialized read from this allocation, so it is unique and
        # we can recycle its name
        # val = self.getSolver().freshValue(f"uninit_{frm.asValue()}", 8 * bytesNum)
        val = self.getSolver().Var(f"uninit_{frm.asValue()}", 8 * bytesNum)
        # write the fresh value into memory, so that
        # later reads see the same value.
        # If an error occurs, just propagate it up
        err = state.memory.write(ptr, val)

        return val, err

    def read(self, state, toOp, fromOp, bytesNum):
        assert isinstance(bytesNum, int), f"Invalid number of bytes: {bytesNum}"
        frm = state.get(fromOp)
        if frm is None:
            self.lazyAllocate(state, fromOp)
            frm = state.get(fromOp)

        assert frm.is_pointer()
        if not frm.getOffset().is_concrete():
            state.setKilled("Read with non-constant offset not supported yet")
            return [state]
        try:
            val, err = state.memory.read(frm, bytesNum)
            if err:
                assert err.isMemError()
                if err.isUninitRead():
                    val, err = self.uninitializedRead(state, fromOp, frm, bytesNum)
                    assert isinstance(toOp, Load)
                    state.addNondet(NondetLoad.fromExpr(val, toOp, fromOp))

        except NotImplementedError as e:
            state.setKilled(str(e))
            return [state]
        if err:
            state.setError(err)
        else:
            state.set(toOp, val)
        return [state]
