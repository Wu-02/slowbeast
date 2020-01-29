from .. interpreter.executionstate import ExecutionState


class SEState(ExecutionState):
    """ Execution state of symbolic execution """

    def __init__(self, pc=None):
        ExecutionState.__init__(self, pc)
        self.pathCondition = None

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
        ExecutionState.copyTo(self, rhs)
        rhs.pathCondition = self.pathCondition

    def copy(self):
        new = SEState()
        self.copyTo(new)
        return new
