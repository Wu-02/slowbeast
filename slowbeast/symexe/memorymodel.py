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
# to use core.Memory. symexe.Memory overrides uninitialized reads in the Memory() object
# in a way that is not suitable for lazy memory
class LazySymbolicMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)
        # over-approximate unsupported operations
        self._overapprox_unsupported = True

    def lazyAllocate(self, state, op):
        assert isinstance(op, Alloc) or isinstance(op, GlobalVariable)
        s = self.allocate(state, op)
        assert len(s) == 1 and s[0] is state
        dbgv("Lazily allocated {0}".format(op), color="WHITE")
        assert state.get(op), "Did not bind an allocated value"

    def _havoc_ptr_target(self, state, ptr):
        """ Havoc memory possibly pointed by ptr"""
        # we do not know what we write where, so just clear all the information if possible
        mo = state.memory.get_obj(ptr.object())
        if mo:
            state.memory.havoc((mo,))
        else:
            state.memory.havoc()
            return [state]

    def write(self, state, instr, valueOp, toOp):
        to = state.get(toOp)
        if to is None:
            self.lazyAllocate(state, toOp)
            to = state.get(toOp) # FIXME "We're calling get() method but we could return the value..."
        assert to.is_pointer()
        if not to.offset().is_concrete(): # FIXME: move this check to memory.write() object
            if self._overapprox_unsupported:
                self._havoc_ptr_target(state, to)
            else:
                state.setKilled("Write with non-constant offset not supported yet")
            return [state]

        value = state.try_eval(valueOp)
        if value is None:
            value = state.solver().Var(
                f"uninit_{valueOp.as_value()}", IntType(8 * instr.bytewidth())
            )
        assert isinstance(value, Value)

        err = state.memory.write(to, value)
        if err:
            assert err.isMemError()
            if err.isUnsupported() and self._overapprox_unsupported:
                self._havoc_ptr_target(state, to)
            else:
                state.setError(err)
        return [state]

    def uninitializedRead(self, state, frm, ptr, bytesNum):
        dbgv("Reading nondet for uninitialized value: {0}".format(ptr), color="WHITE")
        # NOTE: this name identifier is reserved for value representing
        # uninitialized read from this allocation, so it is unique and
        # we can recycle its name
        # val = self.solver().fresh_value(f"uninit_{frm.as_value()}", 8 * bytesNum)
        val = state.solver().Var(f"uninit_{frm.as_value()}", IntType(8 * bytesNum))
        # write the fresh value into memory, so that
        # later reads see the same value.
        # If an error occurs, just propagate it up
        if ptr.offset().is_concrete():
            err = state.memory.write(ptr, val)
            if err and self._overapprox_unsupported and err.isUnsupported():
                err = self._havoc_ptr_target(state, ptr)
        elif self._overapprox_unsupported:
            err = self._havoc_ptr_target(state, ptr)

        return val, err

    def read(self, state, toOp, fromOp, bytesNum):
        assert isinstance(bytesNum, int), f"Invalid number of bytes: {bytesNum}"
        frm = state.get(fromOp)
        if frm is None:
            self.lazyAllocate(state, fromOp)
            frm = state.get(fromOp)

        assert frm.is_pointer()
        if not frm.offset().is_concrete():
            if self._overapprox_unsupported:
                val, err = self.uninitializedRead(state, fromOp, frm, bytesNum)
                if err:
                    state.setError(err)
                else:
                    state.set(toOp, val)
                return [state]
            else:
                state.setKilled("Read with non-constant offset not supported yet")
            return [state]
        val, err = state.memory.read(frm, bytesNum)
        if err:
            assert err.isMemError(), err
            if err.isUninitRead():
                val, err = self.uninitializedRead(state, fromOp, frm, bytesNum)
                assert isinstance(toOp, Load)
                state.addNondet(NondetLoad.fromExpr(val, toOp, fromOp))
            elif err.isUnsupported() and self._overapprox_unsupported:
                val, err = self.uninitializedRead(state, fromOp, frm, bytesNum)
        if err:
            state.setError(err)
        else:
            state.set(toOp, val)
        return [state]
