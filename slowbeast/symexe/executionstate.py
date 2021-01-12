from ..core.executionstate import ExecutionState
from ..util.debugging import warn, FIXME
from .constraints import ConstraintsSet, IncrementalConstraintsSet
from copy import copy
from sys import stdout


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
        return self._solver.is_sat(*self.getConstraints(), *e)

    def isfeasible(self):
        """
        Solve the PC and return True if it is sat. Handy in the cases
        when the state is constructed manually.
        """
        return self._solver.is_sat(*self.getConstraints())

    def concretize(self, *e):
        return self._solver.concretize(self.getConstraints(), *e)

    def input_vector(self):
        return self.concretize(*self.getNondets())

    def model(self):
        return {
            x: c
            for (x, c) in zip(self.getNondets(), self.concretize(*self.getNondets()))
        }

    def concretize_with_assumptions(self, assumptions, *e):
        return self._solver.concretize(self.getConstraints() + assumptions, *e)

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = SEState(self._executor, self.pc, self.memory, self._solver)
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

    def addNondet(self, n):
        if self._nondets_ro:
            self._nondets = copy(self._nondets)
            self._nondets_ro = False
        # we can have only one nonded for a given allocation
        assert not n.isNondetLoad() or all(
            map(
                lambda x: x.alloc != n.alloc,
                (l for l in self._nondets if l.isNondetLoad()),
            )
        )
        self._nondets.append(n)

    def getNondets(self):
        return self._nondets

    def getNondetLoads(self):
        return (l for l in self._nondets if l.isNondetLoad())

    def getNondetLoadOf(self, alloc):
        for n in self._nondets:
            if n.isNondetLoad() and n.alloc == alloc:
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
