from copy import copy
from sys import stdout

from slowbeast.core.state import ExecutionState
from slowbeast.ir.instruction import (
    Alloc,
    GlobalVariable,
    Load,
    ThreadJoin,
    Store,
    Call,
    Return,
)
from .nondetinput import NondetInput
from ..solvers.symcrete import solve_incrementally
from slowbeast.util.debugging import ldbgv
from .constraints import IncrementalConstraintsSet
from typing import Optional, TextIO, Union
from slowbeast.symexe.constraints import ConstraintsSet
from slowbeast.symexe.memory import Memory


class SEState(ExecutionState):
    """Execution state of symbolic execution"""

    __slots__ = (
        "_executor",
        "_solver",
        "_constraints",
        "_constraints_ro",
        "_id",
        "_nondets",
        "_nondets_ro",
    )
    statesCounter = 0

    def __init__(
        self,
        executor=None,
        pc=None,
        memory: Optional[Memory] = None,
        solver=None,
        constraints=None,
    ) -> None:
        super().__init__(pc, memory)

        SEState.statesCounter += 1
        self._id = SEState.statesCounter

        self._executor = executor
        self._solver = solver
        self._constraints = constraints or ConstraintsSet()
        self._constraints_ro = False
        # a sequence of nondets as met on this path
        self._nondets = []
        self._nondets_ro = False


    def get_id(self):
        return self._id

    def __eq__(self, rhs: object):
        """Syntactic comparison"""
        assert (
            self._executor is rhs._executor
        ), f"Comparing execution states of different executors: {self._executor}, {rhs.executor}"
        return super().__eq__(rhs) and self._constraints == rhs._constraints

    def solver(self):
        return self._solver

    def executor(self):
        return self._executor

    def expr_manager(self):
        return self.solver().expr_manager()

    def is_sat(self, *e):
        # XXX: check whether this kind of preprocessing is not too costly
        symb = []
        for x in e:
            if x.is_concrete():
                assert isinstance(x.value(), bool)
                if not x.value():
                    return False
                continue
            symb.append(x)
        if not symb:
            return True

        r = self.solver().try_is_sat(1000, *self.constraints(), *e)
        if r is not None:
            return r

        return solve_incrementally(self.constraints(), e, self.expr_manager())

    def try_is_sat(self, timeout, *e):
        return self.solver().try_is_sat(timeout, *self.constraints(), *e)

    def is_feasible(self):
        """
        Solve the PC and return True if it is sat. Handy in the cases
        when the state is constructed manually.
        """
        C = self.constraints()
        if not C:
            return True
        r = self.solver().try_is_sat(1000, *C)
        if r is not None:
            return r

        em = self.expr_manager()
        return solve_incrementally([], C, em)

    def concretize(self, *e):
        return self.solver().concretize(self.constraints(), *e)

    def concretize_with_assumptions(self, assumptions, *e):
        return self.solver().concretize(self.constraints() + assumptions, *e)

    def input_vector(self):
        return self.concretize(*self.nondet_values())

    def model(self):
        return dict(zip(self.nondet_values(), self.concretize(*self.nondet_values())))

    def _copy_to(self, new: ExecutionState) -> ExecutionState:
        assert new is not self
        assert new.get_id() != self.get_id()
        super()._copy_to(new)  # cow copy of super class

        new._executor = self._executor
        new._solver = self._solver
        new._constraints = self._constraints
        new._constraints_ro = True
        self._constraints_ro = True

        new._nondets = self._nondets
        new._nondets_ro = True
        self._nondets_ro = True

        return new

    def constraints(self):
        return self._constraints.get()

    def constraints_obj(self):
        return self._constraints

    def path_condition(self):
        return self._constraints.as_formula(self.solver().expr_manager())

    def add_constraint(self, *C) -> None:
        if self._constraints_ro:
            self._constraints = self._constraints.copy()
            self._constraints_ro = False

        for c in C:
            self._constraints.add(c)

    def set_constraints(self, *C) -> None:
        if len(C) == 1 and isinstance(C[0], ConstraintsSet):
            self._constraints = C[0]
            self._constraints_ro = False
        else:
            self._constraints = type(self._constraints)()
            self._constraints_ro = False
            self.add_constraint(*C)

    def create_nondet(self, instr, val) -> None:
        """
        Create a new non-deterministic input with value 'val' caused by
        instruction 'instr'.
        """
        # self.add_nondet(Nondet(instr, NondetInstrResult.from_expr(val, instr)))
        self.add_nondet_input(NondetInput(instr, val))

    def add_nondet_input(self, n: NondetInput) -> None:
        """
        Register new non-deterministic input to the state.
        """
        assert isinstance(n, NondetInput), n
        if self._nondets_ro:
            self._nondets = copy(self._nondets)
            self._nondets_ro = False
        # we can have only one nonded for a given allocation
        if n.is_nondet_load() and self.nondet_load_of(n.alloc) is not None:
            raise RuntimeError(
                "Multiple nondets of the same load unsupported atm: "
                f"n:{n}, nondets: {self._nondets}"
            )
        self._nondets.append(n)

    def has_nondets(self) -> bool:
        return len(self._nondets) > 0

    def nondet(self, x):
        for nd in self._nondets:
            if nd.instruction == x:
                return nd
        return None

    def nondets(self):
        return self._nondets

    def nondet_values(self):
        return (nd.value for nd in self._nondets)

    def nondet_loads(self):
        return (l for l in self._nondets if isinstance(l.instruction, Load))

    def nondet_load_of(self, alloc):
        raise NotImplementedError("Not Implemented")
        #  for n in self._nondets:
        #      if n.is_nondet_load() and n.alloc == alloc:
        #          return n
        #  return None

    def dump(self, stream: TextIO = stdout) -> None:
        super().dump(stream)
        write = stream.write
        write(" -- nondets --\n")
        for n in self._nondets:
            write(str(n))
            write("\n")
        write(" -- constraints --\n")
        write(str(self.constraints_obj()))
        write("\n")


class IncrementalSEState(SEState):
    def __init__(self, executor=None, pc=None, m=None) -> None:
        C = IncrementalConstraintsSet()
        super().__init__(executor, pc, m, solver=None, constraints=C)

    def solver(self):
        return self._constraints.solver()


class LazySEState(SEState):
    # def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
    #    super().__init__(executor, pc, m, solver, constraints)

    def get_nondet_instr_result(self):
        return (l for l in self._nondets if l.is_nondet_instr_result())

    def havoc(self, mobjs=None) -> None:
        self.memory.havoc(mobjs)
        if mobjs:
            newnl = []
            get = self.get
            get_obj = self.memory.get_obj
            for l in self._nondets:
                if l.is_nondet_load():
                    alloc = get(l.alloc)
                    if alloc and get_obj(alloc.object()) in mobjs:
                        newnl.append(l)
            self._nondets = newnl
        else:
            self._nondets = []

    def eval(self, v: Union[Alloc, GlobalVariable]):
        value = self.try_eval(v)
        if value is None:
            vtype = v.type()
            if vtype.is_pointer():
                if isinstance(
                    v, (Alloc, GlobalVariable)
                ):  # FIXME: this is hack, do it generally for pointers
                    self.executor().memorymodel.lazy_allocate(self, v)
                    return self.try_eval(v)
                name = f"unknown_ptr_{v.as_value()}"
            else:
                name = f"unknown_{v.as_value()}"
            value = self.solver().symbolic_value(name, v.type())
            ldbgv(
                "Created new nondet value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.create_nondet(v, value)
        return value


class Thread:
    __slots__ = "pc", "cs", "_id", "_paused", "_detached", "_in_atomic", "_exit_val"

    # ids = 0

    def __init__(self, tid, pc, callstack) -> None:
        self.pc = pc
        self.cs = callstack  # callstack
        self._id = tid  # Thread.ids
        self._paused = False
        self._detached = False
        self._in_atomic = False
        self._exit_val = None
        # Thread.ids += 1

    def copy(self) -> "Thread":
        n = copy(self)  # shallow copy
        n.cs = self.cs.copy()
        return n

    def get_id(self):
        return self._id

    def is_detached(self) -> bool:
        return self._detached

    def set_detached(self) -> None:
        self._detached = True

    def pause(self) -> None:
        assert not self._paused
        self._paused = True

    def unpause(self) -> None:
        assert self._paused
        self._paused = False

    def is_paused(self) -> bool:
        return self._paused

    def set_atomic(self, b: bool) -> None:
        if b:
            self._in_atomic += 1
        else:
            self._in_atomic -= 1
        assert self._in_atomic >= 0

    def in_atomic(self) -> bool:
        return self._in_atomic > 0

    def __str__(self) -> str:
        s = f"Thread({self.get_id()}@{self.pc}"
        if self.is_paused():
            s += ", paused"
        if self.is_detached():
            s += ", detached"
        if self.in_atomic():
            s += f", in atomic seq (nest lvl {self._in_atomic})"
        if self._exit_val is not None:
            s += f", exited with {self._exit_val}"
        return s + ")"

    def __repr__(self) -> str:
        return f"Thread[{self.get_id()}: pc: {self.pc}, cs: {self.cs}]"


def _get_event(pc: Union[Call, Load, Return, Store, ThreadJoin]) -> int:
    if isinstance(pc, Store):
        return Event.WRITE
    if isinstance(pc, Load):
        return Event.READ
    if isinstance(pc, Call):
        if pc.called_function().name() == "pthread_mutex_lock":
            return Event.LOCK
        if pc.called_function().name() == "pthread_mutex_unlock":
            return Event.UNLOCK
        return Event.CALL
    if isinstance(pc, ThreadJoin):
        return Event.CALL
    if isinstance(pc, Return):
        return Event.RET
    raise NotImplementedError(f"Unknown event: {pc}")


def _get_mem(evty, pc: ThreadJoin, state):
    if evty == Event.WRITE:
        return state.eval(pc.operand(1))
    if evty in (Event.READ, Event.LOCK, Event.UNLOCK):
        return state.eval(pc.operand(0))
    if evty == Event.CALL:
        if isinstance(pc, ThreadJoin):
            return "join"
        return pc.called_function().name()
    if evty == Event.RET:
        return None
    raise NotImplementedError(f"Unknown event: {pc}")


def _get_val(evty, pc, state):
    if evty == Event.WRITE:
        return state.eval(pc.operand(0))
    return None


def _evty_to_str(ty) -> str:
    if ty == Event.WRITE:
        return "write"
    if ty == Event.READ:
        return "read"
    if ty == Event.LOCK:
        return "lock"
    if ty == Event.UNLOCK:
        return "unlock"
    if ty == Event.CALL:
        return "call"
    if ty == Event.RET:
        return "ret"
    return "invalid event"


class Event:
    WRITE = 1
    READ = 2
    LOCK = 3
    UNLOCK = 4
    CALL = 5
    RET = 6

    __slots__ = "ty", "mem", "val"

    def __init__(self, state) -> None:
        pc = state.pc
        self.ty = _get_event(pc)
        self.mem = _get_mem(self.ty, pc, state)
        self.val = _get_val(self.ty, pc, state)

    def is_call_of(self, call: str):
        if isinstance(call, str):
            return self.ty == Event.CALL and self.mem == call
        return self.ty == Event.CALL and self.mem in call

    def conflicts(self, ev):
        """Does this event conflicts with the given event 'ev'?"""
        ty, evty = self.ty, ev.ty
        mem, evmem = self.mem, ev.mem
        # joins are not conflicting

        if ty == Event.READ:
            if evty == Event.READ:
                return False
            if evty == Event.WRITE:
                if mem.is_concrete() and evmem.is_concrete():
                    return mem == evmem
            return True  # are we conflicting with all the locks?
        if ty == Event.WRITE:
            if evty == Event.WRITE:
                if mem.is_concrete() and evmem.is_concrete():
                    if mem == evmem:
                        if self.val == ev.val:
                            return False
                        return True
                return True
            if evty == Event.READ:
                if mem.is_concrete() and evmem.is_concrete():
                    return mem == evmem
            return True  # are we conflicting with all the locks?
        if ty in (Event.LOCK, Event.UNLOCK) and evty in (Event.LOCK, Event.UNLOCK):
            return mem == evmem
        # FIXME: we should probably do better
        return True

    def __str__(self) -> str:
        return f"{_evty_to_str(self.ty)} of {self.mem}, val: {self.val}"


