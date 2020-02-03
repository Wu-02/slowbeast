from .. interpreter.executionstate import ExecutionState
from .. util.debugging import dbg
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

    def getID(self):
        return self._id

    def __eq__(self, rhs):
        return super(SEState, self).__eq__(rhs) and\
            self.constraints == rhs.constraints

    def copyTo(self, rhs):
        assert isinstance(rhs, SEState)
        dbg('FIXME: add copy on write to SE state')
        super(SEState, self).copyTo(rhs)
        rhs.constraints = self.constraints.copy()

    def copy(self):
        new = SEState()
        self.copyTo(new)
        return new

    def getConstraints(self):
        return self.constraints.get()

    def getConstraintsObj(self):
        return self.constraints

   # def setPathCondition(self, pc):
   #    if isinstance(pc, list):
   #        self.pathCondition = ConstraintsSet(pc)
   #    else:
   #        self.pathCondition = pc

    def addConstraint(self, *C):
        for c in C:
            self.constraints.addConstraint(c)

    def dump(self):
        ExecutionState.dump(self)
        print(" -- constraints --")
        print(self.getConstraintsObj())
