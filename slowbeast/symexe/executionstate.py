from slowbeast.core.executionstate import ExecutionState
from slowbeast.util.debugging import warn, ldbgv
from slowbeast.ir.instruction import Alloc, GlobalVariable, Load
from .constraints import ConstraintsSet, IncrementalConstraintsSet
from slowbeast.solvers.solver import solve_incrementally
from copy import copy
from sys import stdout


class Nondet:
    __slots__ = "instruction", "value"

    def __init__(self, instr, val):
        self.instruction = instr
        self.value = val

    def is_nondet_call(self):
        return False

    def is_nondet_load(self):
        return False

    def is_nondet_instr(self):
        return True

    def __repr__(self):
        return f"{self.instruction.as_value()} = {self.value}"


class SEState(ExecutionState):
    """ Execution state of symbolic execution """

    # XXX do not store warnings in the state but keep them in a map in the interpreter or so?
    __slots__ = (
        "_executor",
        "_solver",
        "_constraints",
        "_constraints_ro",
        "_id",
        "_warnings",
        "_warnings_ro",
        "_nondets",
        "_nondets_ro",
    )
    statesCounter = 0

    def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
        super().__init__(pc, m)

        SEState.statesCounter += 1
        self._id = SEState.statesCounter

        self._executor = executor
        self._solver = solver
        self._constraints = constraints or ConstraintsSet()
        self._constraints_ro = False
        # a sequence of nondets as met on this path
        self._nondets = []
        self._nondets_ro = False

        self._warnings = []
        self._warnings_ro = False

    def get_id(self):
        return self._id

    def __eq__(self, rhs):
        """ Syntactic comparison """
        assert (
            self._executor is rhs._executor
        ), "Comparing execution states of different executors"
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
                else:
                    continue
            else:
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
        return {
            x: c
            for (x, c) in zip(
                self.nondet_values(), self.concretize(*self.nondet_values())
            )
        }

    def _copy_to(self, new):
        super()._copy_to(new)  # cow copy of super class

        new._executor = self._executor
        new._solver = self._solver
        new._constraints = self._constraints
        new._constraints_ro = True
        self._constraints_ro = True

        new._warnings = self._warnings
        new._warnings_ro = True
        self._warnings_ro = True

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

    def add_constraint(self, *C):
        if self._constraints_ro:
            self._constraints = self._constraints.copy()
            self._constraints_ro = False

        for c in C:
            self._constraints.add(c)

    def set_constraints(self, *C):
        if len(C) == 1 and isinstance(C[0], ConstraintsSet):
            self._constraints = C[0]
            self._constraints_ro = False
        else:
            self._constraints = type(self._constraints)()
            self._constraints_ro = False
            self.add_constraint(*C)

    def add_warning(self, msg):
        warn(msg)
        if self._warnings_ro:
            self._warnings = copy(self._warnings)
            self._warnings_ro = False
        self._warnings.append(msg)

    def warnings(self, msg):
        return self._warnings

    def create_nondet(self, instr, val):
        # self.add_nondet(Nondet(instr, NondetInstrResult.fromExpr(val, instr)))
        self.add_nondet(Nondet(instr, val))

    def add_nondet(self, n):
        assert isinstance(n, Nondet), n
        if self._nondets_ro:
            self._nondets = copy(self._nondets)
            self._nondets_ro = False
        # we can have only one nonded for a given allocation
        if n.is_nondet_load() and self.nondet_load_of(n.alloc) is not None:
            raise RuntimeError(
                f"Multiple nondets of the same load unsupported atm: n:{n}, nondets: {self._nondets}"
            )
        self._nondets.append(n)

    def has_nondets(self):
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
        raise NotImplemented("Not Implemented")
        for n in self._nondets:
            if n.is_nondet_load() and n.alloc == alloc:
                return n
        return None

    def dump(self, stream=stdout):
        ExecutionState.dump(self, stream)
        write = stream.write
        write(" -- nondets --\n")
        for n in self._nondets:
            write(str(n))
            write("\n")
        write(" -- constraints --\n")
        write(str(self.constraints_obj()))
        write("\n")

class IncrementalSEState(SEState):
    def __init__(self, executor=None, pc=None, m=None):
        C = IncrementalConstraintsSet()
        super().__init__(executor, pc, m,
                         solver=None, constraints=C)

    def solver(self):
        return self._constraints.solver()


class LazySEState(SEState):
    def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)

    def get_nondet_instr_result(self):
        return (l for l in self._nondets if l.is_nondet_instr_result())

    def havoc(self, mobjs=None):
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

    def eval(self, v):
        value = self.try_eval(v)
        if value is None:
            vtype = v.type()
            if vtype.is_pointer():
                if isinstance(
                    v, (Alloc, GlobalVariable)
                ):  # FIXME: this is hack, do it generally for pointers
                    self.executor().memorymodel.lazyAllocate(self, v)
                    return self.try_eval(v)
                name = f"unknown_ptr_{v.as_value()}"
            else:
                name = f"unknown_{v.as_value()}"
            value = self.solver().Var(name, v.type())
            ldbgv(
                "Created new nondet value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.create_nondet(v, value)
        return value

class ThreadedSEState(SEState):
    __slots__ = "_threads", "_current_thread"

    def __init__(self, executor=None, pc=None, m=None, solver=None, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)
        self._threads = [(pc, self.memory.get_cs() if m else None)]
        self._current_thread = 0

    def _copy_to(self, new):
        super()._copy_to(new)
        new._threads = [(self.pc, self.memory.get_cs()) if idx == self._current_thread else (t[0], t[1].copy()) for (idx, t) in enumerate(self._threads)]
        new._current_thread = self._current_thread

    def schedule(self, idx):
        print('# scheduling ', idx)
        assert idx < len(self._threads)
        self._threads[self._current_thread] = (self.pc, self.memory.get_cs())

        self.pc = self._threads[idx][0]
        self.memory.set_cs(self._threads[idx][1])
        self._current_thread = idx

    def add_thread(self, pc):
        pair = (pc, self.memory.get_cs().copy())
        self._threads.append(pair)
        return pair

    def threads(self):
        return self._threads
