from ..ir.instruction import Alloc, GlobalVariable
from slowbeast.domains.value import Value
from .memory import Memory


class MemoryModel:
    """
    Class that takes care of performing memory operations
    (without knowing what is the real memory implementation)
    """

    def __init__(self, opts):
        self._opts = opts

    def createMemory(self):
        """
        Create a memory object that is going to be a part
        of a state.
        """
        return Memory()

    def allocate(self, state, instr):
        """
        Perform the allocation by the instruction
        "inst" and return the new states (there may be
        several new states, e.g., one where the allocation succeeds,
        one where it fails, etc.).
        """
        assert isinstance(instr, Alloc) or isinstance(instr, GlobalVariable)
        size = state.eval(instr.size())
        if instr.is_global():
            ptr = state.memory.allocateGlobal(instr)
        else:
            ptr = state.memory.allocate(size, instr)
        state.set(instr, ptr)
        return [state]

    def write(self, state, instr, valueOp, toOp):
        value = state.eval(valueOp)
        to = state.get(toOp)
        if to is None:
            state.setKilled("Use of unknown variable: {0}".format(toOp))
            return [state]

        assert isinstance(value, Value)
        assert to.is_pointer()
        if not to.offset().is_concrete():
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

    def read(self, state, toOp, fromOp, bytesNum):
        frm = state.get(fromOp)
        if frm is None:
            state.setKilled("Use of unknown variable: {0}".format(fromOp))
            return [state]

        assert frm.is_pointer()
        if not frm.offset().is_concrete():
            state.setKilled("Read with non-constant offset not supported yet")
            return [state]
        try:
            val, err = state.memory.read(frm, bytesNum)
        except NotImplementedError as e:
            state.setKilled(str(e))
            return [state]
        if err:
            state.setError(err)
        else:
            state.set(toOp, val)
        return [state]
