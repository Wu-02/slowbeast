from .. interpreter.executionstate import ExecutionState

class SEState(ExecutionState):

    def __init__(self, pc):
        ExecutionState.__init__(self, pc)
        self.pathCondition = True

    def getPathCondition(self):
        return self.pathCondition

    def setPathCondition(self, pc):
        self.pathCondition = pc

    def dump(self):
        super(ExecutionState, self).dump()
        print(" -- path condition --")
        print(self.getPathCondition())

    def copyTo(self, rhs):
        assert isinstance(rhs, SEState)
        new = SEState()
        super(ExecutionState, self).copyTo(new)
        rhs.pathCondition = self.pathCondition

    def copy(self):
        new = SEState()
        self.copyTo(new)
        return new
