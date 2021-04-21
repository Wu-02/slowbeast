from sys import stdout
from slowbeast.domains.value import Value
from slowbeast.domains.pointer import Pointer
from slowbeast.ir.instruction import Alloc, GlobalVariable
from slowbeast.ir.types import IntType, BoolType, get_offset_type, get_size_type
from slowbeast.core.errors import MemError
from slowbeast.core.memorymodel import MemoryModel as CoreMM
from slowbeast.symexe.memory import Memory as SEMemory


def _nondet_value(fresh, op, bitsnum):
    if op.type().is_bool():
        return fresh(f"unknown_bool_{op.as_value()}", BoolType())
    if op.type().is_pointer():
        ptrobj = fresh(f"unknown_obj_{op.as_value()}", get_offset_type())
        ptroff = fresh(f"unknown_off_{op.as_value()}", get_offset_type())
        return Pointer(ptrobj, ptroff)
    return fresh(f"uninit_{op.as_value()}", IntType(bitsnum))


# FIXME: do we need to inherit from SEMemory?
class BSEMemory(SEMemory):
    def __init__(self):
        super().__init__()
        # output state of memory
        self._reads = {}
        self._input_reads = {}

    def _copy_to(self, new):
        super()._copy_to(new)
        new._reads = self._reads.copy()
        new._input_reads = self._input_reads.copy()
        return new

    def read_symbolic_ptr(self, state, toOp, fromOp, bitsnum=None):
        raise NotImplementedError("Not implemented yet")

    # val = _nondet_value(state.solver().fresh_value, toOp, bitsnum)
    # state.create_nondet(toOp, val)
    # state.set(toOp, val)
    # self._reads[fromOp] = val

    def _symbolic_read(self, state, ptr, valinst, bytesNum):
        val = self._reads.get(ptr)
        if val:
            if val.bytewidth() != bytesNum:
                return None, MemError(
                    MemError.UNSUPPORTED,
                    f"Read of value with different sizes: {val} {bytesNum}",
                )
            return val, None
        if not ptr.object().is_concrete() or not ptr.offset().is_concrete():
            val = _nondet_value(state.solver().fresh_value, valinst, bytesNum * 8)
            state.create_nondet(valinst, val)
            self._reads[ptr] = val
            self._input_reads[ptr] = (val, bytesNum)
            return val, None
        raise NotImplementedError("Not implemented")
        # concrete read

    def read(self, ptr, bytesNum):
        v = self._reads.get(ptr)
        if v is None:
            return None, MemError(
                MemError.UNSUPPORTED, f"Read of unknown value; pointer: {ptr}"
            )
        if v.bytewidth() != bytesNum:
            return None, MemError(
                MemError.UNSUPPORTED,
                f"Read of value with different sizes: {v} {bytesNum}",
            )
        return v, None

    def write_symbolic_ptr(self, state, toOp, value):
        raise NotImplementedError("Not implemented yet")
        # reading from this pointer must equal value in the future
        # self._reads[toOp] = value

    def symbolic_write(self, ptr, value):
        self._reads[ptr] = value

    def dump(self, stream=stdout):
        stream.write("-- Global objects:\n")
        for o in self._glob_objects.values():
            o.dump(stream)
        stream.write("-- Global bindings:\n")
        for g, v in self._glob_bindings.items():
            stream.write("{0} -> {1}\n".format(g.as_value(), v.as_value()))
        stream.write("-- Objects:\n")
        for o in self._objects.values():
            o.dump(stream)
        stream.write("-- Reads:\n")
        if self._reads:
            for p, x in self._reads.items():
                stream.write(f"+L({p.as_value()})={x}\n")
        stream.write("-- Call stack:\n")
        self._cs.dump(stream)


# BSESymbolicMemoryModel inherints from CoreMM intentionally (
# symexe.Memory overrides uninitialized reads in the Memory() object
# in a way that is not suitable for lazy memory
class BSEMemoryModel(CoreMM):
    def __init__(self, opts):
        super().__init__(opts)

    def create_memory(self):
        """
        Create a memory object that is going to be a part
        of a state.
        """
        return BSEMemory()

    def allocate(self, state, instr):
        """
        Perform the allocation by the instruction
        "inst" and return the new states (there may be
        several new states, e.g., one where the allocation succeeds,
        one where it fails, etc.).
        """
        if isinstance(instr, (Alloc, GlobalVariable)):
            size = instr.size()
        else:
            size = state.solver().Var(f"ndt_size_{instr.as_value()}", get_size_type())
        size = state.try_eval(size)
        if instr.is_global():
            ptr = state.memory.allocate_global(instr)
        else:
            ptr = state.memory.allocate(size, instr)
        state.set(instr, ptr)
        return [state]

    def write(self, state, instr, valueOp, toOp):
        M = state.memory

        value = state.eval(valueOp)
        assert value, "Have no value after (symbolic) eval"
        assert isinstance(value, Value)

        to = state.eval(toOp)
        if not to.is_pointer():
            M.write_symbolic_ptr(state, toOp, value)
            return [state]

        M.symbolic_write(to, value)
        return [state]

    def read(self, state, toOp, fromOp, bytesNum, bitsnum=None):
        """
        We want to read 'bitsnum' of bits and in order to do that
        we read 'bytesNum' of bytes
        """
        assert (
            bitsnum is None or max(1, int(bitsnum / 8)) == bytesNum
        ), f"{bytesNum} {bitsnum}"
        assert isinstance(bytesNum, int), f"Invalid number of bytes: {bytesNum}"
        M = state.memory
        frm = state.eval(fromOp)
        if not frm.is_pointer():
            M.read_symbolic_ptr(state, toOp, fromOp, bitsnum or bytesNum * 8)
            return [state]

        assert frm.is_pointer(), frm
        val, err = M._symbolic_read(state, frm, toOp, bytesNum)
        if err:
            assert err.is_memory_error(), err
            state.set_error(err)
        else:
            state.set(toOp, val)
        return [state]
