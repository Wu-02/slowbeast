from slowbeast.domains.symbolic import NondetInstrResult, _desimplify_ext
from slowbeast.core.executionstate import ExecutionState
from slowbeast.util.debugging import warn, ldbgv
from slowbeast.ir.instruction import Alloc, GlobalVariable
from .constraints import ConstraintsSet, IncrementalConstraintsSet
from slowbeast.solvers.solver import IncrementalSolver
from copy import copy
from sys import stdout

def _sort_subs(subs):
    """
    Return multiplication of two variables later than other expressions
    """
    #FIXME: not very efficient
    V = []
    for k, v in subs.items():
        s = sum(map(lambda c: not c.is_concrete(), k.children()))
        if s > 1:
            V.append((k, v))
        else:
            yield (k,v)
    for k, v in V:
        yield (k, v)

def try_solve_incrementally(assumptions, exprs, em):
    if assumptions:
        # First try to rewrite the formula into simpler form
        expr1 = em.conjunction(*exprs).rewrite_polynomials(assumptions)
        A = []
        for i in range(len(assumptions)):
            a = assumptions[i]
            A.append(a.rewrite_polynomials([x for n, x in enumerate(assumptions) if n != i]))
        assumptions = A
        r = IncrementalSolver().try_is_sat(3000, *assumptions, expr1)
        if r is not None:
            return r
        expr = em.conjunction(*assumptions, expr1)
    else:
        expr = em.conjunction(*assumptions, *exprs)

    ###
    # Now try abstractions
    #
    rexpr, subs = expr.replace_arith_ops()
    if rexpr:
        solver = IncrementalSolver()
        solver.add(rexpr.rewrite_and_simplify())
        for placeholder, e in _sort_subs(subs):
            if solver.is_sat() is False:
                return False
            solver.add(em.Eq(e, placeholder))
        # solve the un-abstracted expression
        return solver.try_is_sat(1000)
    # FIXME try reduced bitwidth and propagating back models
    return None
 

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

    def __init__(self, executor, pc, m, solver, constraints=None):
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
        return self._solver.expr_manager()

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

        r = self._solver.try_is_sat(1000, *self.getConstraints(), *e)
        if r is not None:
            return r

        conj = self.expr_manager().conjunction
        assumptions = conj(*self.getConstraints())
        expr = conj(*e)
        r = try_solve_incrementally(self.getConstraints(), e, self.expr_manager())
        if r is not None:
            return r
        return self._solver.is_sat(expr)

    def isfeasible(self):
        """
        Solve the PC and return True if it is sat. Handy in the cases
        when the state is constructed manually.
        """
        return self._solver.is_sat(*self.getConstraints())

    def concretize(self, *e):
        return self._solver.concretize(self.getConstraints(), *e)

    def input_vector(self):
        return self.concretize(*self.nondets())

    def model(self):
        return {
            x: c for (x, c) in zip(self.nondets(), self.concretize(*self.nondets()))
        }

    def concretize_with_assumptions(self, assumptions, *e):
        return self._solver.concretize(self.getConstraints() + assumptions, *e)

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        # also, use type(self) so that this method works also for
        # child classes (if not overridden)
        new = type(self)(self._executor, self.pc, self.memory, self._solver)
        super().copyTo(new)  # cow copy of super class

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

    def getConstraints(self):
        return self._constraints.get()

    def getConstraintsObj(self):
        return self._constraints

    def path_condition(self):
        return self._constraints.as_formula(self._solver.expr_manager())

    def addConstraint(self, *C):
        if self._constraints_ro:
            self._constraints = self._constraints.copy()
            self._constraints_ro = False

        for c in C:
            self._constraints.add(c)

    def setConstraints(self, C):
        self._constraints = C
        self._constraints_ro = False

    def addWarning(self, msg):
        warn(msg)
        if self._warnings_ro:
            self._warnings = copy(self._warnings)
            self._warnings_ro = False
        self._warnings.append(msg)

    def getWarnings(self, msg):
        return self._warnings

    def add_nondet(self, n):
        if self._nondets_ro:
            self._nondets = copy(self._nondets)
            self._nondets_ro = False
        # we can have only one nonded for a given allocation
        if n.is_nondet_load() and self.getNondetLoadOf(n.alloc) is not None:
            raise RuntimeError(f"Multiple nondets of the same load unsupported atm: n:{n}, nondets: {self._nondets}")
        self._nondets.append(n)

    def nondets(self):
        return self._nondets

    def getNondetLoads(self):
        return (l for l in self._nondets if l.is_nondet_load())

    def getNondetLoadOf(self, alloc):
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
        write(str(self.getConstraintsObj()))
        write("\n")


class IncrementalSEState(SEState):
    def __init__(self, executor, pc, m, solver=None):
        if solver:  # copy ctor
            super().__init__(executor, pc, m, None, None)
        else:
            C = IncrementalConstraintsSet()
            super().__init__(executor, pc, m, C.solver(), C)

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = IncrementalSEState(self._executor, self.pc, self.memory)
        super().copyTo(new)  # cow copy of super class

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


class LazySEState(SEState):
    def __init__(self, executor, pc, m, solver, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)
        # this is basically the input vector for this state.
        # A state describes a set of executions by putting constraints
        # on the inputs. But when inputs are created dynamically during
        # the execution, we must put constraints on them once they are
        # created. Those are these constraints.
        self._future_nondets = {}  # instr -> [expr]

    def get_nondet_instr_result(self):
        return (l for l in self._nondets if l.is_nondet_instr_result())

    def get_future_nondet(self, instr):
        exprs = self._future_nondets.get(instr)
        if exprs:
            return exprs.pop(0)  # consume the returned expression
        return None

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
                name = f"nondet_ptr_{v.as_value()}"
            else:
                name = f"nondet_{v.as_value()}"
            value = self.solver().Var(name, v.type())
            ldbgv(
                "Created new nondet value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.add_nondet(NondetInstrResult.fromExpr(value, v))
        return value
