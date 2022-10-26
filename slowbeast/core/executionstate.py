from sys import stdout

from slowbeast.core.executionstatus import ExecutionStatus
from slowbeast.domains.concrete_value import ConcreteBool, ConcreteVal
from slowbeast.domains.pointer import Pointer
from slowbeast.ir.function import Function
from slowbeast.ir.types import get_offset_type
from typing import Any, Optional, Union, TextIO


from slowbeast.util.debugging import dbgv
from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.expr import Expr
from slowbeast.ir.instruction import ValueInstruction
from slowbeast.symexe.memory import Memory


class ExecutionState:
    __slots__ = "pc", "memory", "_status"

    def __init__(self, pc: None = None, m: Optional[Memory] = None) -> None:
        # program counter
        self.pc = pc
        # memory objects
        self.memory = m
        # status of the execution: ready/exited/errored/etc.
        self._status = ExecutionStatus()

    def __eq__(self, rhs: object) -> bool:
        if self is rhs:
            return True
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
        assert self.has_error() or self.is_terminated() or self.was_killed(), self
        return self._status.detail()

    def was_killed(self) -> bool:
        return self._status.is_killed()

    def set_killed(self, e) -> None:
        self._status.set_killed(e)

    def set_exited(self, ec: ConcreteBitVec) -> None:
        self._status.set_exited(ec)

    def set_terminated(self, reason) -> None:
        self._status.set_terminated(reason)

    def is_terminated(self) -> bool:
        return self._status.is_terminated()

    def exited(self) -> bool:
        return self._status.is_exited()

    def get_exit_code(self):
        assert self.exited()
        return self._status.detail()

    def status(self) -> ExecutionStatus:
        return self._status

    def is_ready(self) -> bool:
        return self._status.is_ready()

    def eval(self, v: Any) -> Union[ConcreteBool, ConcreteBitVec, Expr]:
        # FIXME: make an attribute is_constant...
        if isinstance(v, ConcreteVal):
            return v
        if isinstance(v, Pointer) and v.is_null():
            return v
        if isinstance(v, Function):
            return ConcreteBitVec(v.get_id(), get_offset_type())
        value = self.get(v)
        if value is None:
            raise RuntimeError(f"Use of uninitialized/unknown variable {v}")
        return value

    def try_eval(self, v: ConcreteBitVec) -> ConcreteBitVec:
        if isinstance(v, ConcreteVal):
            return v
        if isinstance(v, Pointer) and v.is_null():
            return v
        return self.get(v)

    def set(
        self, what: ValueInstruction, v: Union[ConcreteBitVec, Pointer, Expr]
    ) -> None:
        """Associate a value to a register (in the current stack frame)"""
        if __debug__:
            h = f" ({hex(v.value())})" if v and v.is_concrete() and v.is_bv() else ""
            dbgv("[{0}] -> {1}{2}".format(what, v, h), color="GREEN")
        # XXX: rename to bind?
        self.memory.set(what, v)

    def get(self, v: ValueInstruction) -> Union[ConcreteBitVec, Pointer, Expr]:
        """
        Get a value from a register (in the current stack frame or globals)
        """
        return self.memory.get(v)

    def globals_list(self):
        """Return the list of globals in this state"""
        return self.memory.globals_list()

    def values_list(self):
        return self.memory.values_list()

    def push_call(
        self, callsite: None, fun: Optional[Function] = None, args_mapping: None = None
    ) -> None:
        """
        Push a new frame to the call stack. Callsite and fun can be None
        in the cases where we create dummy states and we just need some
        frame on the stack.
        """
        assert fun or not callsite, "Got no fun by some callsite..."
        self.memory.push_call(callsite, fun, args_mapping or {})
        if fun:
            self.pc = fun.bblock(0).instruction(0)

    def pop_call(self) -> None:
        return self.memory.pop_call()

    def frame(self, idx: int = -1):
        return self.memory.frame(idx)

    def dump(self, stream: TextIO = stdout) -> None:
        stream.write("---- State ----\n")
        self._status.dump(stream)
        stream.write(" -- program counter --\n")
        stream.write(f"{self.pc}\n")
        stream.write("-- Memory:\n")
        self.memory.dump(stream)
