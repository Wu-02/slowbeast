from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.executionstate import LazySEState

class BSEState(LazySEState):
    def __init__(self, executor, pc, m, solver, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)

class Executor(PathExecutor):
    """
    Symbolic Executor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(self, solver, opts, memorymodel=None):
        super().__init__(solver, opts, memorymodel)

    def createState(self, pc=None, m=None):
        """
        Overridden method for creating states.
        Since the path may not be initial, we must use states
        that are able to lazily create unknown values
        """
        if m is None:
            m = self.getMemoryModel().createMemory()
        s = BSEState(self, pc, m, self.solver)
        assert not s.getConstraints(), "the state is not clean"
        return s

    def execute_edge(self, states, edge,
                     pre=None, post=None,
                     annot_before_loc=None, annot_after_loc=None):
        """
        states - pre-condition states (execute from these states)
        """
        assert all(map(lambda s: isinstance(s, LazySEState), states))

        source, target = edge.source(), edge.target()
        ready, nonready = states, []
        # annotations before taking the edge (proably an invariant)
        execannot = self.execute_annotations
        if pre:
            ready, tu = execannot(ready, pre)
            nonready += tu
        # annotations before source
        locannot = annot_before_loc(source) if annot_before_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after source
        locannot = annot_after_loc(source) if annot_after_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_call() and not edge.called_function().isUndefined():
            fn = edge.called_function().name()
            for s in ready:
                s.setTerminated(f"Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        # annotations before target
        locannot = annot_before_loc(target) if annot_before_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after target
        locannot = annot_after_loc(target) if annot_after_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        if post:
            ready, tu = execannot(ready, post)
            nonready += tu

        return ready, nonready
