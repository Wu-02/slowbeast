from slowbeast.interpreter.interpreter import Interpreter, ExecutionOptions
from slowbeast.solvers.solver import Solver
from slowbeast.domains.symbolic import Future
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from slowbeast.core.errors import AssertFailError
from slowbeast.ir.instruction import Call

from .executor import Executor as SExecutor


class FutureExecutor(SExecutor):
    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        if self.is_error_fn(fun):
            state.setError(AssertFailError(f"Called '{fun.getName()}'"))
            return [state]

        if fun.isUndefined():
            return self.execUndefFun(state, instr, fun)

        if self.callsForbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.setKilled(
                "calling '{0}', but calls are forbidden".format(fun.getName())
            )
            return [state]

        nexti = instr.get_next_inst()
        # if we have no next instr, execute normally
        if False or nexti is None:  # execute normally
            # map values to arguments
            assert len(instr.getOperands()) == len(fun.getArguments())
            mapping = {
                x: state.eval(y)
                for (x, y) in zip(fun.getArguments(), instr.getOperands())
            }
            state.pushCall(instr, fun, mapping)
            return [state]
        else:
            retTy = fun.getReturnType()
            futureval = state.getExprManager().freshValue("future", retTy.bitwidth())
            future = Future(futureval.unwrap(), futureval.type(), instr, state)
            newstate = state.copy()
            newstate.set(instr, future)
            newstate.addNondet(future)
            newstate.pc = nexti  # continue executing the next instruction
            newstate.dump()
            # FIXME: clear the state (the function may modify globals)
            return [newstate]


class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super(SEOptions, self).__init__(opts)
        if opts:
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
            self.error_funs = opts.error_funs
        else:
            self.concretize_nondets = False
            self.uninit_is_nondet = False
            self.exit_on_error = False
            self.error_funs = []


class SEStats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0


class FutureSymbolicExecutor(Interpreter):
    def __init__(
        self,
        P,
        ohandler=None,
        opts=SEOptions(),
        executor=None,
        ExecutorClass=FutureExecutor,
    ):
        self.solver = Solver()
        super().__init__(P, opts, executor or ExecutorClass(self.solver, opts))
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler

    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

    def getSolver(self):
        return self.solver

    def getNextState(self):
        states = self.states
        if not states:
            return None

        # DFS for now
        return states.pop()

    def handleNewStates(self, newstates):
        hs = self.handleNewState
        for s in newstates:
            hs(s)

    def handleNewState(self, s):
        testgen = self.ohandler.testgen if self.ohandler else None
        stats = self.stats
        if s.isReady():
            self.states.append(s)
        elif s.hasError():
            print_stderr(
                "{0}: {1}, {2}".format(s.get_id(), s.pc, s.getError()), color="RED"
            )
            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.processState(s)
            if self.getOptions().exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return
        elif s.isTerminated():
            print_stderr(s.getError(), color="BROWN")
            stats.paths += 1
            stats.terminated_paths += 1
            if testgen:
                testgen.processState(s)
        elif s.wasKilled():
            stats.paths += 1
            stats.killed_paths += 1
            print_stderr(s.getStatusDetail(), prefix="KILLED STATE: ", color="WINE")
            if testgen:
                testgen.processState(s)
        else:
            assert s.exited()
            dbg("state exited with exitcode {0}".format(s.getExitCode()))
            stats.paths += 1
            stats.exited_paths += 1
            if testgen:
                testgen.processState(s)
