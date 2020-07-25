from .. core.executionstate import ExecutionState
from .. util.debugging import warn, FIXME
from . constraints import ConstraintsSet
from copy import copy
from sys import stdout


class SEState(ExecutionState):
    """ Execution state of symbolic execution """
    statesCounter = 0

    def __init__(self, pc, m, solver):
        ExecutionState.__init__(self, pc, m)
        self._solver = solver
        self.constraints = ConstraintsSet()

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
            self.constraints == rhs.constraints

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

    def concretize(self, *e):
        return self._solver.concretize(self.getConstraints(), *e)

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = SEState(self.pc, self.memory, self.getSolver())
        super(SEState, self).copyTo(new)  # cow copy of super class

        new.constraints = self.constraints.copy()
        new._warnings = self._warnings
        new._warnings_ro = True
        self._warnings_ro = True

        new._nondets = self._nondets
        new._nondets_ro = True
        self._nondets_ro = True

        return new

    def getConstraints(self):
        return self.constraints.get()

    def getConstraintsObj(self):
        return self.constraints

    def addConstraint(self, *C):
        for c in C:
            self.constraints.addConstraint(c)

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
        self._nondets.append(n)

    def getNondets(self):
        return self._nondets

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
