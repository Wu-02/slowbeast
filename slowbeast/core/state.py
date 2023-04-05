from sys import stdout
from typing import Optional, Union, TextIO

from slowbeast.core.executionstatus import ExecutionStatus
from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.expr import Expr
from slowbeast.domains.pointer import Pointer
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import ValueInstruction
from slowbeast.ir.types import get_offset_type
from slowbeast.symexe.memory import Memory

# from slowbeast.util.debugging import dbgv


class ExecutionState:
    __slots__ = "pc", "memory", "_status"

    def __init__(self, pc: None = None, m: Optional[Memory] = None) -> None:
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # status of the execution: ready/exited/error/etc.
        self._status = ExecutionStatus()

    def __eq__(self, rhs: object) -> bool:
        if self is rhs:
            return True
        # For now assert that we compare to other state instead
        # of returning False. Comparing to something else
        # means probably a bug.
        assert isinstance(rhs, ExecutionState)
        assert self.pc is not None and rhs.pc is not None
        return (
            self.pc == rhs.pc
            and self._status == rhs._status
            and self.memory == rhs.memory
        )

    def _copy_to(self, rhs: "ExecutionState") -> None:
        assert isinstance(rhs, ExecutionState)
        rhs.pc = self.pc
        rhs.memory = self.memory.copy()
        rhs._status = self._status.copy()

    def copy(self) -> "ExecutionState":
        # do not use copy.copy() so that we bump the id counter
        # also, use type(self) so that this method works also for
        # child classes (if not overridden)
        new = type(self)()
        self._copy_to(new)
        return new

    def status_detail(self):
        return self._status.detail()

    def set_error(self, e) -> None:
        self._status.set_error(e)

    def has_error(self) -> bool:
        return self._status.is_error()

    def get_error(self):
        assert self.has_error() or self.is_terminated() or self.is_killed(), self
        return self._status.detail()

    def is_killed(self) -> bool:
        return self._status.is_killed()

    def set_killed(self, e) -> None:
        self._status.set_killed(e)

    def set_exited(self, ec: ConcreteBitVec) -> None:
        self._status.set_exited(ec)

    def set_terminated(self, reason) -> None:
        self._status.set_terminated(reason)

    def is_terminated(self) -> bool:
        return self._status.is_terminated()

    # TODO: remove in the future
    def exited(self) -> bool:
        return self._status.is_exited()

    def is_exited(self) -> bool:
        return self._status.is_exited()

    def get_exit_code(self):
        assert self.exited(), self
        return self._status.detail()

    def status(self) -> ExecutionStatus:
        return self._status

    def is_ready(self) -> bool:
        return self._status.is_ready()

    def eval(self, v):
        """
        Take an IR value representation and get its value in this state,
        e.g., for a register x123 return 0 if the register is 0 in this state.
        Raise an exception if the value is not set in this state and it is not
        a constant or other value that can be evaluated.
        """
        value = self.try_eval(v)
        if value is None:
            raise RuntimeError(f"Use of uninitialized/unknown variable {v}")
        return value

    def try_eval(self, v):
        """
        Take an IR value representation and get its value in this state,
        e.g., for a register x123 return 0 if the register is 0 in this state.
        Return None if the value is not set in this state and it is not
        a constant or other value that can be evaluated.
        """
        if isinstance(v, ConcreteVal):
            return v
        if isinstance(v, Pointer) and v.is_null():
            return v
        if isinstance(v, Function):
            return ConcreteBitVec(v.get_id(), get_offset_type())

        return self.get(v)

    def set(
        self, what: ValueInstruction, v: Union[ConcreteBitVec, Pointer, Expr]
    ) -> None:
        """
        Associate a value to with a register (in the current stack frame).

        It holds that:
          self.set(x, v)
          assert self.eval(x) == v
        """
        # if __debug__:
        #    h = f" ({hex(v.value())})" if v and v.is_concrete() and v.is_bv() else ""
        #    dbgv(f"[{what}] -> {v}{h}", color="green", verbose_lvl=3)
        # XXX: rename to bind?
        self.memory.set(what, v)

    def get(self, v: ValueInstruction) -> Union[ConcreteBitVec, Pointer, Expr]:
        """
        Get a value from a register (in the current stack frame or globals).
        Return None if the value is not set.
        """
        return self.memory.get(v)

    def globals_list(self):
        """Return the list of globals in this state"""
        return self.memory.globals_list()

    def values_list(self):
        """List of all set values (registers)"""
        return self.memory.values_list()

    def push_call(
        self, callsite: None, fun: Optional[Function] = None, args_mapping: None = None
    ) -> None:
        """
        Push a new frame to the call stack. Callsite and fun can be None
        in the cases where we create dummy states and we just need some
        frame on the stack.
        `args_mapping` provides the mapping between the call function's parameters
        and actual call values.
        """
        assert fun or not callsite, "Got no fun by some callsite..."
        # push a new stack frame
        self.memory.push_call(callsite, fun, args_mapping or {})
        if fun:
            # change the PC of the state to the first instruction of the function
            self.pc = fun.bblock(0).instruction(0)

    def pop_call(self) -> None:
        """
        Pop the last stack frame from the call stack after the current function
        call is finished.
        """
        return self.memory.pop_call()

    def frame(self, idx: int = -1):
        """
        Get a stack frame on index `idx` (by default the current stack frame)
        """
        return self.memory.frame(idx)

    def dump(self, stream: TextIO = stdout) -> None:
        stream.write("---- State ----\n")
        self._status.dump(stream)
        stream.write(" -- program counter --\n")
        stream.write(f"{self.pc}\n")
        stream.write("-- Memory:\n")
        self.memory.dump(stream)
