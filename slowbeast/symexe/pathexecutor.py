from typing import Optional, Sized

from ..core.executionresult import split_nonready_states, PathExecutionResult
from slowbeast.symexe.executionstate import LazySEState
from slowbeast.symexe.memorymodel import SymbolicMemoryModel
from slowbeast.util.debugging import dbgv, ldbgv
from .annotations import execute_annotations
from .iexecutor import IExecutor as SExecutor


class PathExecutor(SExecutor):
    """
    Symbolic PathExecutor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(
        self, program, solver, opts, memorymodel: Optional[SymbolicMemoryModel] = None
    ) -> None:
        super().__init__(program, solver, opts, memorymodel)

    def create_state(self, pc=None, m=None) -> LazySEState:
        """
        Overridden method for creating states.
        Since the path may not be initial, we must use states
        that are able to lazily create unknown values
        """
        if m is None:
            m = self.get_memory_model().create_memory()
        s = LazySEState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s

    def exec_undef_fun(self, state, instr, fun):
        name = fun.name()
        if name == "abort":
            state.set_terminated("Aborted via an abort() call")
            return [state]

        retTy = fun.return_type()
        if retTy:
            val = state.solver().fresh_value(name, retTy)
            state.create_nondet(instr, val)
            state.set(instr, val)
        state.pc = state.pc.get_next_inst()
        return [state]

    def execute_annotations(self, states, annots):
        assert all(map(lambda s: isinstance(s, LazySEState), states))
        # if there are no annotations, return the original states
        if not annots:
            return states, []

        ready = []
        nonready = []

        for s in states:
            ts, tu = execute_annotations(self, s, annots)
            ready += ts
            nonready += tu
        assert all(map(lambda s: isinstance(s, LazySEState), ready)), "Wrong state type"
        return ready, nonready

    def _exec_assume_edge(self, states, edge):
        nonready = []
        isnot = edge.assume_false()
        for elem in edge:
            newstates = []
            for r in states:
                cond = r.eval(elem)
                # if cond is None:
                #    r.set_terminated(f"Invalid assume edge: {elem}")
                #    nonready.append(r)
                #    continue
                ldbgv(
                    "assume {0}{1}",
                    ("not " if isnot else "", cond),
                    verbose_lvl=3,
                    color="dark_green",
                )
                tmp = self.exec_assume_expr(
                    r, r.expr_manager().Not(cond) if isnot else cond
                )
                for t in tmp:
                    if t.is_ready():
                        newstates.append(t)
                    else:
                        nonready.append(t)
            states = newstates

        return states, nonready

    def _execute_annotated_edge(self, states, edge, path, pre=None):
        assert all(map(lambda s: isinstance(s, LazySEState), states))

        source = edge.source()
        ready, nonready = states, []
        # annotations before taking the edge (proably an invariant)
        execannot = self.execute_annotations
        if pre:
            ready, tu = execannot(ready, pre)
            nonready += tu
        # annotations before source
        locannot = path.annot_before_loc(source) if path else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after source
        locannot = path.annot_after_loc(source) if path else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_call() and not edge.called_function().is_undefined():
            fn = edge.called_function().name()
            for s in ready:
                s.set_terminated(f"Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        return ready, nonready

    def execute_annotated_path(
        self, state, path: Sized, invariants=None
    ) -> PathExecutionResult:
        """
        Execute the given path through CFG with annotations from the given
        state. NOTE: the passed states may be modified.

        All error and killed states met during the execution are counted
        as early terminated unless they are generated _after_ reaching
        the last location on the path. That is, the error states
        are those generated by annotations that follow the last location
        on the path.

        The method does not take into account whether the the last
        location is error or not. This must be handled in the top-level code.
        I.e., if the last location is error location, then the result.ready
        states are in fact error states (those that reach the error location
        and pass the annotations of this location).

        Invariants are assume annotations 'before' locations.
        """

        if isinstance(state, list):
            states = state
        else:
            states = [state]

        assert all(
            map(lambda s: isinstance(s, LazySEState), states)
        ), "Wrong state type"

        result = PathExecutionResult()
        earlytermstates = []
        edges = path.edges()
        execannots = self.execute_annotations

        # execute the precondition of the path
        pre = path.annot_before()
        if pre:
            states, tu = execannots(states, pre)
            earlytermstates += tu

        pathlen = len(path)
        assert all(
            map(lambda s: isinstance(s, LazySEState), states)
        ), "Wrong state type"
        for idx in range(pathlen):
            edge = edges[idx]
            dbgv(f"vv ----- Edge {edge} ----- vv", verbose_lvl=3)
            states, nonready = self._execute_annotated_edge(
                states,
                edge,
                path,
                invariants.get(edge.source()) if invariants else None,
            )
            assert all(
                map(lambda s: isinstance(s, LazySEState), states)
            ), "Wrong state type"
            assert all(map(lambda x: x.is_ready(), states))
            assert all(map(lambda x: not x.is_ready(), nonready))

            # now execute the branch following the edge on the path
            earlytermstates += nonready

            dbgv(f"^^ ----- Edge {edge} ----- ^^", verbose_lvl=3)
            if not states:
                dbgv("^^ (-8 Infeasible path 8-) ^^", verbose_lvl=3)
                break

        if states:
            # execute the annotations of the target (as _execute_annotated_edge
            # executes only the annotations of the source to avoid repetition)
            dbgv(">> Annotation of last loc + post", verbose_lvl=3)
            target = edge.target()
            locannot = path.annot_before_loc(target)
            if locannot and states:
                states, tu = execannots(states, locannot)
                # this annotation also counts as early terminating  as we still didn't
                # virtually get to the final location of the path
                earlytermstates += tu

            errors, other = [], []
            locannot = path.annot_after_loc(target)
            if locannot and states:
                states, tu = execannots(states, locannot)
                err, oth = split_nonready_states(tu)
                if err:
                    errors.extend(err)
                if oth:
                    other.extend(oth)
            # execute the postcondition of the path
            post = path.annot_after()
            if post and states:
                states, tu = execannots(states, post)
                err, oth = split_nonready_states(tu)
                if err:
                    errors.extend(err)
                if oth:
                    other.extend(oth)

            result.errors = errors or None
            result.other = other or None

        result.ready = states or None
        result.early = earlytermstates or None

        assert result.check(), "The states were partitioned incorrectly"
        return result
