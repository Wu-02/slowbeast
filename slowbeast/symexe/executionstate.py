from .. interpreter.executionstate import ExecutionState
from .. util.debugging import dbg, warn, FIXME
from . memory import SymbolicMemory
from copy import deepcopy


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

    def __init__(self, pc, m):
        ExecutionState.__init__(self, pc, m)
        self.constraints = ConstraintsSet()

        SEState.statesCounter += 1
        self._id = SEState.statesCounter
        self._warnings = []

    def getID(self):
        return self._id

    def __eq__(self, rhs):
        return super(SEState, self).__eq__(rhs) and\
            self.constraints == rhs.constraints

    def copyTo(self, rhs):
        assert isinstance(rhs, SEState)
        FIXME('add copy on write to SE state')
        super(SEState, self).copyTo(rhs)
        rhs.constraints = self.constraints.copy()

    def copy(self):
        new = SEState(self.pc, self.memory)
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

    def dump(self):
        ExecutionState.dump(self)
        print(" -- constraints --")
        print(self.getConstraintsObj())
