from queue import Queue as FIFOQueue
from typing import Optional #, Union

from slowbeast.kindse.programstructure import ProgramStructure
from slowbeast.symexe.annotations import AssumeAnnotation
from slowbeast.util.debugging import print_stdout, dbg, ldbgv, print_stderr

from slowbeast.symexe.symbolicexecution import (
    SymbolicExecutor as SymbolicInterpreter,
)
from slowbeast.core.executor import PathExecutionResult
from .bseexecutor import Executor as BSEExecutor, BSEState
from slowbeast.bse.memorymodel import BSEMemoryModel
from slowbeast.kindse.naive.naivekindse import Result
from slowbeast.kindse import KindSEOptions


def report_state(stats, n, fn=print_stderr):
    if n.hasError():
        if fn:
            fn(
                "state {0}: {1}, {2}".format(n.get_id(), n.pc, n.getError()),
                color="RED",
            )
        stats.errors += 1
    elif n.wasKilled():
        if fn:
            fn(n.getStatusDetail(), prefix="KILLED STATE: ", color="WINE")
        stats.killed_paths += 1


def check_paths(executor, paths, pre=None, post=None):
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.add_annot_after(post.as_assert_annotation())

        if pre:
            p.add_annot_before(pre.as_assume_annotation())

        r = executor.execute_annotated_path(p)
        result.merge(r)

    return result

class BSEContext:
    """ Class that keeps the state of BSE search """

    __slots__ = "edge", "err"

    def __init__(self, edge, err):
        """
        edge  - edge after which the error should be infeasible
        error - error condition
        """
        assert isinstance(err, (AssumeAnnotation, BSEState)), err
        self.edge = edge
        self.err = err

    def __repr__(self):
        err = self.err
        return f"BSE-ctx[{self.edge}:{err}]"

class BackwardSymbolicInterpreter(SymbolicInterpreter):
    def __init__(
        self, prog, ohandler=None, opts=KindSEOptions(), programstructure=None, invariants=None
    ):
        super().__init__(
            P=prog, ohandler=ohandler, opts=opts, ExecutorClass=BSEExecutor
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = BSEMemoryModel(opts)
        indexecutor = BSEExecutor(self.solver(), opts, memorymodel)
        dbg("Forbidding calls in BSE executor for now")
        indexecutor.forbid_calls()
        self._indexecutor = indexecutor

        if programstructure is None:
            programstructure = ProgramStructure(prog, self.new_output_file)
        self.programstructure = programstructure

        self.invariant_sets = {} if invariants is None else invariants

        self._entry_loc = programstructure.entry_loc
        # as we run the executor in nested manners,
        # we want to give different outputs
        self.reportfn = print_stdout

        # states to search (we could use some more efficient implementation?)
        self.queue = FIFOQueue()
        # states that were killed due to some problem
        self.problematic_states = []
        # here we report error states
        self.return_states = None

    def ind_executor(self):
        return self._indexecutor

    def problematic_paths_as_result(self):
        r = PathExecutionResult()
        r.other = self.problematic_states
        return r

    def get_cfa(self, F):
        assert self.programstructure.cfas.get(F), f"Have no CFA for function {F.name()}"
        return self.programstructure.cfas.get(F)

    def get_return_states(self):
        """
        The states that caused killing the execution,
        i.e., error states or killed states
        """
        return self.return_states

    def _execute_edge(self, bsectx, fromInit=False, invariants=None):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        assert isinstance(bsectx, BSEContext), bsectx
        if fromInit:
            # we must execute without lazy memory
            executor = self.executor()
            if not self.states:
                self.prepare()
            states = [s.copy() for s in self.states]
            assert states

            ldbgv("Computing (init) precondition: {0}", (bsectx,), fn=self.reportfn, color="orange")
        else:
            executor = self.ind_executor()
            s = executor.createCleanState()
            states = [s]

            ldbgv("Computing precondition: {0}", (bsectx,), fn=self.reportfn, color="orange")

        assert all(
            map(lambda s: not s.getConstraints(), states)
        ), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        ready, nonready = executor.execute_edge(states, bsectx.edge, invariants=invariants)
        for s in (s for s in nonready if s.wasKilled() or s.hasError()):
            report_state(self.stats, s, self.reportfn)
            self.problematic_states.append(s)

        state = bsectx.err
        assert len(ready) <= 1, "We support only one pre-state"
        if ready:
            if state.join_prestate(ready[0]):
                return [state]
        return []
        #prestates = []
        #for r in ready:
        #    prestates.extend(r.apply_postcondition(poststate))
        #return prestates

    def precondition(self, bsectx : BSEContext) -> (Result, Optional[BSEState]):
        """ Compute precondition of the given BSEContext. """
        edge = bsectx.edge

        if edge.source() is self._entry_loc:
            prestates = self._execute_edge(bsectx, fromInit=True)
            assert len(prestates) <= 1, "Maximally one pre-states is supported atm"
            if prestates:
                # found a real error
                return Result.UNSAFE, prestates[0]
            if not self._entry_loc.has_predecessors():
                return Result.SAFE, None

        prestates = self._execute_edge(bsectx, invariants=self.invariant_sets)
        assert len(prestates) <= 1, "Maximally one pre-states is supported atm"
        if prestates:
            return Result.UNKNOWN, prestates[0]
        return Result.SAFE, None

    def get_next_state(self):
        queue = self.queue
        if queue.empty():
            return None
        return queue.get_nowait()

    def queue_state(self, s):
        self.queue.put_nowait(s)
        assert not self.queue.empty(), list(self.queue)

    def extend_state(self, bsectx, postcondition):
        assert postcondition, postcondition
        had_one : bool = False
        for edge in bsectx.edge.predecessors():
            self.queue_state(BSEContext(edge, postcondition.copy() if had_one else postcondition))
            had_one = True
