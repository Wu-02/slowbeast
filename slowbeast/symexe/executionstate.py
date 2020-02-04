from .. interpreter.executionstate import ExecutionState
from .. util.debugging import dbg, warn, FIXME
from . memory import SymbolicMemory
from copy import deepcopy, copy
from sys import stdout


class ConstraintsSet:
    def __init__(self, C=[]):
        self.constraints = C

    def copy(self):
        return deepcopy(self)

    def __eq__(self, rhs):
        return self.constraints == rhs.constraints

    def addConstraint(self, *C):
        for c in C:
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
        return self._solver.is_sat(*self.getConstraints(), *e)

    def copyTo(self, rhs):
        assert isinstance(rhs, SEState)
        FIXME('add copy on write to SE state')
        super(SEState, self).copyTo(rhs)
        rhs.constraints = self.constraints.copy()
        rhs._warnings = copy(self._warnings)

    def copy(self):
        new = SEState(self.pc, self.memory, self.getSolver())
        self.copyTo(new)
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
        self._warnings.append(msg)

    def getWarning(self, msg):
        return self._warnings

    def dump(self, stream=stdout):
        ExecutionState.dump(self, stream)
        stream.write(" -- constraints --\n")
        stream.write(str(self.getConstraintsObj()))
        stream.write('\n')
