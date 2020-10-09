from .. core.executionstate import ExecutionState
from .. util.debugging import warn, FIXME
from . constraints import ConstraintsSet
from copy import copy
from sys import stdout


class SEState(ExecutionState):
    """ Execution state of symbolic execution """
    statesCounter = 0

    def __init__(self, pc, m, solver, constraints=ConstraintsSet()):
        C = ConstraintsSet()
        assert not C.get(), C.get()
        ExecutionState.__init__(self, pc, m)

        self._solver = solver
        self._constraints = ConstraintsSet()
        self._constraints_ro = False

        SEState.statesCounter += 1
        self._id = SEState.statesCounter
        self._warnings = []
        self._warnings_ro = False
        # a sequence of nondets as met on this path
        self._nondets = []
        self._nondets_ro = False

    def getID(self):
        return self._id

    def __eq__(self, rhs):
        return super(SEState, self).__eq__(rhs) and\
            self._constraints == rhs._constraints

    def getSolver(self):
        return self._solver

    def getExprManager(self):
        return self._solver.getExprManager()

    def is_sat(self, *e):
        # XXX: check whether this kind of preprocessing is not too costly
        symb = []
        for x in e:
            if x.isConstant():
                assert isinstance(x.getValue(), bool)
                if x.getValue() == False:
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

    def concretize_with_assumptions(self, assumptions, *e):
        return self._solver.concretize(self.getConstraints() + assumptions, *e)

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = SEState(self.pc, self.memory, self.getSolver())
        super(SEState, self).copyTo(new)  # cow copy of super class

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

    def addConstraint(self, *C):
        if self._constraints_ro:
            self._constraints = self._constraints.copy()
            self._constraints_ro = False

        for c in C:
            self._constraints.addConstraint(c)

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
        assert not n.isNondetLoad() or all(map(lambda x: x.alloc != n.alloc,
                                               (l for l in self._nondets if l.isNondetLoad())))
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
            write('\n')
        write(" -- constraints --\n")
        write(str(self.getConstraintsObj()))
        write('\n')
