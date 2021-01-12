from slowbeast.util.debugging import dbgv
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import Alloc, GlobalVariable, Load
from slowbeast.ir.types import IntType
from slowbeast.domains.symbolic import NondetLoad
from slowbeast.symexe.memory import Memory
from slowbeast.core.memorymodel import MemoryModel as CoreMM


class SymbolicMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)

    def createMemory(self):
        """ Create a memory object that is going to be a part of a state. """
        return Memory()


# LazySymbolicMemoryModel inherints from CoreMM intentionally (SymbolicMemoryModel
# redefined uninitialized reads)
class LazySymbolicMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)

    def lazyAllocate(self, state, op):
        assert isinstance(op, Alloc) or isinstance(op, GlobalVariable)
        s = self.allocate(state, op)
        assert len(s) == 1 and s[0] is state
        dbgv("Lazily allocated {0}".format(op), color="WHITE")
        assert state.get(op), "Did not bind an allocated value"

    def write(self, state, instr, valueOp, toOp):
        to = state.get(toOp)
        if to is None:
            self.lazyAllocate(state, toOp)
            # FIXME "We're calling get() method but we could return the value..."
            to = state.get(toOp)
        assert to.is_pointer()
        if not to.offset().is_concrete():
            # FIXME: move this check to memory.write() object
            state.setKilled("Write with non-constant offset not supported yet")
            return [state]

        value = state.try_eval(valueOp)
        if value is None:
            value = state.getSolver().Var(
                f"uninit_{valueOp.as_value()}", IntType(8 * instr.bytewidth())
            )
        assert isinstance(value, Value)

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
        # val = self.getSolver().freshValue(f"uninit_{frm.as_value()}", 8 * bytesNum)
        val = state.getSolver().Var(f"uninit_{frm.as_value()}", IntType(8 * bytesNum))
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
        if not frm.offset().is_concrete():
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
