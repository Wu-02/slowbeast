from .. core.executionstate import ExecutionState
from .. util.debugging import dbg, warn, FIXME
from . memory import SymbolicMemory
from copy import copy
from sys import stdout


class ConstraintsSet:
    def __init__(self, C=[]):
        self.constraints = C
        self._ro = False

    def copy(self):
        new = copy(self)
        new._ro = True
        return new

    def __eq__(self, rhs):
        return self.constraints == rhs.constraints

    def addConstraint(self, *C):
        if self._ro:
            # shallow copy should be enough
            self.constraints = copy(self.constraints)
            self._ro = False

        for c in C:
            assert not c.isConstant(), "Adding True or False, catch these cases atm"
            self.constraints.append(c)

    def get(self):
        return self.constraints

    def __repr__(self):
        return self.constraints.__repr__()


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

    def copy(self):
        # do not use copy.copy() so that we bump the id counter
        new = SEState(self.pc, self.memory, self.getSolver())
        FIXME("Move CallStack to memory, we create extra empty CS here in the ctor")
        super(SEState, self).copyTo(new)  # cow copy of super class

        new.constraints = self.constraints.copy()
        new._warnings = self._warnings
        new._warnings_ro = True

        return new

    def havoc(self):
        self.constraints = ConstraintsSet()
        self.memory.havoc()
        self._warnings = []
        self._warnings_ro = False

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

    def dump(self, stream=stdout):
        ExecutionState.dump(self, stream)
        stream.write(" -- constraints --\n")
        stream.write(str(self.getConstraintsObj()))
        stream.write('\n')
