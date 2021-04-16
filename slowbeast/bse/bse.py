from queue import Queue as FIFOQueue
from typing import Optional  # , Union

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


def report_state(stats, n, msg=None, fn=print_stderr):
    if n.hasError():
        fn(
            f"{msg if msg else ''}:: state {n.get_id()}: {n.pc}, {n.getError()}",
            color="red",
        )
        stats.errors += 1
    elif n.wasKilled():
        if fn:
            fn(n.getStatusDetail(), prefix="KILLED STATE: ", color="wine")
        stats.killed_paths += 1
    elif n.isTerminated():
        if fn:
            fn(n.getStatusDetail(), prefix="TERMINATED STATE: ", color="orange")
        stats.terminated_paths += 1


class BSEContext:
    """ Class that keeps the state of BSE search """

    __slots__ = "edge", "errorstate", "errordescr"

    def __init__(self, edge, errstate, errdescr=None):
        """
        edge  - edge after which the error should be infeasible
        error - error condition
        """
        assert isinstance(errstate, (AssumeAnnotation, BSEState)), errstate
        self.edge = edge
        self.errorstate = errstate
        self.errordescr = errdescr

    def __repr__(self):
        return f"BSE-ctx[{self.edge}:{self.errorstate}]"


class BackwardSymbolicInterpreter(SymbolicInterpreter):
    def __init__(
        self,
        prog,
        ohandler=None,
        opts=KindSEOptions(),
        programstructure=None,
        invariants=None,
    ):
        super().__init__(
            P=prog, ohandler=ohandler, opts=opts, ExecutorClass=BSEExecutor
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = BSEMemoryModel(opts)
        indexecutor = BSEExecutor(self.solver(), opts, memorymodel)
        # we handle calls explicitely here, so set this to true to catch problems
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

            # ldbgv("Computing (init) precondition: {0}", (bsectx,), fn=self.reportfn, color="orange")
        else:
            executor = self.ind_executor()
            s = executor.createCleanState()
            states = [s]

            # ldbgv("Computing precondition: {0}", (bsectx,), fn=self.reportfn, color="orange")

        assert all(
            map(lambda s: not s.constraints(), states)
        ), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        ready, nonready = executor.execute_edge(
            states, bsectx.edge, invariants=invariants
        )
        for s in (s for s in nonready if s.wasKilled() or s.hasError()):
            report_state(self.stats, s, fn=self.reportfn,
                         msg=f"Executing {bsectx.edge}")
            self.problematic_states.append(s)

        state = bsectx.errorstate
        assert len(ready) <= 1, "We support only one pre-state"
        if ready:
            if state.join_prestate(ready[0]):
                return [state]
        return []
        # prestates = []
        # for r in ready:
        #    prestates.extend(r.apply_postcondition(poststate))
        # return prestates

    def precondition(self, bsectx: BSEContext) -> (Result, Optional[BSEState]):
        """ Compute precondition of the given BSEContext. """
        edge = bsectx.edge

        if edge.source() is self._entry_loc:
            prestates = self._execute_edge(bsectx, fromInit=True)
            assert len(prestates) <= 1, "Maximally one pre-states is supported atm"
            if prestates:
                prestate = prestates[0]
                # FIXME: can we somehow easily check that we do not have to do this?
                # found a real error
                prestate.add_constraint(*prestate.memory_constraints())
                if prestate.isfeasible():
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
        had_one: bool = False
        edge = bsectx.edge
        if edge.has_predecessors():
            for pedge in bsectx.edge.predecessors():
                # if is call edge...
                if pedge.is_call():
                    if not pedge.called_function().is_undefined():
                        self.extend_to_call(pedge, bsectx, postcondition)
                        continue
                    # fall-through
                self.queue_state(
                    BSEContext(
                        pedge,
                        postcondition.copy() if had_one else postcondition,
                        bsectx.errordescr,
                    )
                )
                had_one = True
        elif edge.cfa().is_init(edge):
            # This is entry to procedure. It cannot be the main procedure, otherwise
            # we would either report safe or unsafe, so this is a call of subprocedure
            # that we do not support atm
            self.extend_to_callers(edge.cfa(), bsectx, postcondition)
        # else: dead code, we have nothing to exted

    def extend_to_callers(self, cfa, bsectx, postcondition):
        fun = cfa.fun()
        PS = self.programstructure
        cgnode = PS.callgraph.getNode(fun)
        for callerfun, callsite in cgnode.getCallers():
            calledge = PS.calls[callsite]
            if not calledge.has_predecessors():
                state = postcondition.copy()
                state.setTerminated("Function with only return edge unsupported in BSE atm.")
                report_state(self.stats, state, self.reportfn)
                self.problematic_states.append(state)
                continue
            for pedge in calledge.predecessors():
                state = postcondition.copy()
                n = 0
                # map the arguments to the operands
                for op in callsite.operands():
                    arg = fun.argument(n)
                    val = state.eval(op)
                    argval = state.nondet(arg)
                    if argval is None:
                        n += 1
                        continue
                    state.replace_value(argval.value, val)
                    n += 1
                self.queue_state(BSEContext(pedge, state, bsectx.errordescr))
       #postcondition.setTerminated("Calls unsupported in BSE atm.")
       #report_state(self.stats, postcondition, self.reportfn)
       #self.problematic_states.append(postcondition)

    def extend_to_call(self, edge, bsectx, postcondition):
        PS = self.programstructure
        fun = edge.called_function()
        retval = None
        retnd =  postcondition.nondet(edge[0])
        if retnd is not None:
            retval = retnd.value
            assert fun.return_type() is not None, fun
        for B in fun.ret_bblocks():
            state = postcondition.copy()
            ret = B[-1]
            if retval:
                op = ret.operand(0)
                opval = state.eval(op)
                state.replace_value(retval, opval)
            retedge = PS.rets[ret]
            self.queue_state(BSEContext(retedge, state, bsectx.errordescr))



def check_paths(checker, paths, pre=None, post=None):
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.add_annot_after(post.as_assert_annotation())

        if pre:
            p.add_annot_before(pre.as_assume_annotation())

        r = checker.execute_path(p)
        result.merge(r)

    return result
