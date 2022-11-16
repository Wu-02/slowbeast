from queue import Queue as FIFOQueue
from typing import Optional  # , Union

from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bsestate import BSEState
from slowbeast.bse.memorymodel import BSEMemoryModel
from slowbeast.cfkind import KindSEOptions
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.symexe.interpreter import (
    SymbolicInterpreter as SymbolicInterpreter,
    SEOptions,
)
from slowbeast.util.debugging import print_stdout, print_stderr, dbg, ldbgv
from .bsectx import BSEContext
from .executor import BSELazyPathIExecutor as BSEExecutor
from ..core.executionresult import PathExecutionResult


def report_state(stats, n, msg=None, fn=print_stderr) -> None:
    if n.has_error():
        fn(
            f"{msg if msg else ''}:: state {n.get_id()}: {n.pc}, {n.get_error()}",
            color="red",
        )
        stats.errors += 1
    elif n.was_killed():
        if fn:
            fn(n.status_detail(), prefix="KILLED STATE: ", color="wine")
        stats.killed_paths += 1
    elif n.is_terminated():
        if fn:
            fn(n.status_detail(), prefix="TERMINATED STATE: ", color="orange")
        stats.terminated_paths += 1


class BackwardSymbolicInterpreter(SymbolicInterpreter):
    def __init__(
        self,
        prog,
        ohandler=None,
        opts: KindSEOptions = KindSEOptions(),
        programstructure: Optional[ProgramStructure] = None,
        invariants=None,
    ) -> None:
        super().__init__(
            P=prog, ohandler=ohandler, opts=opts, ExecutorClass=BSEExecutor
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = BSEMemoryModel(opts)
        indexecutor = BSEExecutor(prog, self.solver(), opts, memorymodel)
        self._indexecutor = indexecutor

        if programstructure is None:
            programstructure = ProgramStructure(prog, self.new_output_file)
        self.programstructure = programstructure

        # These invariants will be used during the execution. Note that we take the reference,
        # so they may be changed externally during the execution.
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

    def problematic_paths_as_result(self) -> PathExecutionResult:
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

    def _execute_path(
        self, bsectx: BSEContext, from_init: bool = False, invariants=None
    ):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        assert isinstance(bsectx, BSEContext), bsectx
        if from_init:
            # we must execute without lazy memory
            executor = self.executor()
            if not self.states:
                self.prepare()
            states = [s.copy() for s in self.states]
            assert states

            # ldbgv("Computing (init) precondition: {0}", (bsectx,),
            #       fn=self.reportfn, color="orange")
        else:
            executor = self.ind_executor()
            s = executor.create_clean_state()
            states = [s]

            # ldbgv("Computing precondition: {0}", (bsectx,), fn=self.reportfn, color="orange")

        assert all(map(lambda s: not s.constraints(), states)), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        ready, nonready = executor.execute_bse_path(
            states, bsectx.path, invariants=invariants
        )
        for s in (s for s in nonready if s.was_killed()):
            report_state(
                self.stats, s, fn=self.reportfn, msg=f"Executing {bsectx.path}"
            )
            self.problematic_states.append(s)

        state = bsectx.errorstate
        assert len(ready) <= 1, "We support only one pre-state"
        if ready:
            if state.join_prestate(ready[0], from_init):
                # This assertion must hold only if the execution was maximal
                # - but that may not be tru
                # assert (
                #    not from_init or not state.inputs()
                # ), f"Initial state has unresolved inputs: {state}"
                return [state]
        return []

    def precondition(self, bsectx: BSEContext) -> (Result, Optional[BSEState]):
        """Compute precondition of the given BSEContext."""

        assert isinstance(bsectx.path.source(), CFA.Location)
        assert isinstance(self._entry_loc, CFA.Location)
        if bsectx.path.source() is self._entry_loc:
            prestates = self._execute_path(bsectx, from_init=True)
            assert len(prestates) <= 1, "Maximally one pre-states is supported atm"
            if prestates:
                prestates[0].set_error(bsectx.errordescr)
                return Result.UNSAFE, prestates[0]
            if not self._entry_loc.has_predecessors():
                return Result.SAFE, None

        prestates = self._execute_path(bsectx, invariants=self.invariant_sets)
        assert len(prestates) <= 1, "Maximally one pre-states is supported atm"
        if prestates:
            return Result.UNKNOWN, prestates[0]
        return Result.SAFE, None

    def get_next_state(self):
        queue = self.queue
        if queue.empty():
            return None
        return queue.get_nowait()

    def queue_state(self, s) -> None:
        self.queue.put_nowait(s)
        assert not self.queue.empty(), list(self.queue)

    def replay_state(self, state):
        # FIXME: we do redundant copy, set_input_vector will copy and reverse
        # the list on its own
        ivec = state.input_vector().copy()
        ivec.reverse()
        dbg(f"Input vector: {ivec}")

        class GatherStates:
            class Handler:
                def __init__(self):
                    self.states = []

                def process_state(self, s):
                    self.states.append(s)

            def __init__(self):
                self.testgen = GatherStates.Handler()
                self.states = self.testgen.states

        opts = SEOptions(self.get_options())
        opts.replay_errors = False
        handler = GatherStates()
        SE = SymbolicInterpreter(self.get_program(), handler, opts)
        SE.set_input_vector(ivec)
        SE.run()
        if len(handler.states) != 1:
            return None
        return handler.states[0]

    def extend_state(self, bsectx, postcondition) -> None:
        assert postcondition, postcondition
        had_one: bool = False
        edge = bsectx.path[0]
        # forget the values that we gathered in the forward execution. The only thing
        # that we need to remember are the input reads.
        # FIXME: we could do it more efficiently -- all of it (but we still need the forward execution to work)
        # Maybe have some class just for representing the 'postcondition' that we derive from forward state?
        postcondition.memory.frame().clear()
        if edge.has_predecessors():
            for pedge in edge.predecessors():
                # if predecessor is call edge, continue with the return edges
                # of the called function
                if pedge.is_call():
                    if not pedge.called_function().is_undefined():
                        self.extend_to_call(pedge, bsectx, postcondition)
                        continue
                    # fall-through
                self.queue_state(
                    bsectx.extension(
                        pedge,
                        postcondition.copy() if had_one else postcondition,
                    )
                )
                had_one = True
        elif edge.cfa().is_init(edge):
            # This is entry to procedure. It cannot be the main procedure, otherwise
            # we would either report safe or unsafe, so this is a call of subprocedure
            self.extend_to_callers(edge.cfa(), bsectx, postcondition)
        else:  # dead code, we have nothing to exted
            ldbgv("Nowhere to extend the state", ())

    def extend_to_callers(self, cfa, bsectx, postcondition) -> None:
        # do we entry to some particular call via a call edge?
        cs = postcondition.memory.get_cs()
        if len(cs) > 1:
            # FIXME: maybe create a LazyCallStack that would be bi-directional?
            fun = cs.frame().function
            calledge = postcondition.pop_call()
            self.extend_to_caller(calledge, fun, bsectx, postcondition)
            return

        fun = cfa.fun()
        PS = self.programstructure
        for _, callsite in PS.callgraph.get_node(fun).callers():
            dbg(f"Extending to call-site: {callsite}")
            calledge = PS.calls[callsite]
            self.extend_to_caller(calledge, fun, bsectx, postcondition)

    def extend_to_caller(self, calledge, fun, bsectx, postcondition):
        if not calledge.has_predecessors():
            state = postcondition.copy()
            state.set_terminated(
                "Function with only return edge unsupported in BSE atm."
            )
            report_state(self.stats, state, self.reportfn)
            self.problematic_states.append(state)
            return

        assert len(calledge.elems()) == 1, calledge
        callsite = calledge[0]
        for pedge in calledge.predecessors():
            state = postcondition.copy()
            # map the arguments to the operands
            for n, op in enumerate(callsite.operands()):
                arg = fun.argument(n)
                argval = state.input(arg)
                if argval is None:
                    continue
                state.replace_input_value(argval.value, state.eval(op))
            self.queue_state(bsectx.extension(pedge, state))

    def extend_to_call(self, edge, bsectx, postcondition) -> None:
        """
        Extend the current 'postcondition' backwards via return edges
        of a called function.
        """
        PS = self.programstructure
        fun = edge.called_function()

        # get the return value
        retval = None
        retnd = postcondition.input(edge[0])
        if retnd is not None:
            retval = retnd.value
            assert fun.return_type() is not None, fun

        # extend via return edges
        for B in fun.ret_bblocks():
            state = postcondition.copy()
            state.push_call(edge, fun, {})
            ret = B[-1]
            if retval:
                op = ret.operand(0)
                opval = state.eval(op)
                state.replace_input_value(retval, opval)
            retedge = PS.rets[ret]
            self.queue_state(bsectx.extension(retedge, state))


def check_paths(checker, paths, pre=None, post=None) -> PathExecutionResult:
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
