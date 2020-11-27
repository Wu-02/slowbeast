from slowbeast.interpreter.interpreter import Interpreter, ExecutionOptions
from slowbeast.solvers.solver import Solver
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from .executor import Executor as SExecutor


class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super(SEOptions, self).__init__(opts)
        if opts:
            self.replay_errors = opts.replay_errors
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
            self.error_funs = opts.error_funs
        else:
            self.replay_errors = False
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


class SymbolicExecutor(Interpreter):
    def __init__(
        self, P, ohandler=None, opts=SEOptions(), executor=None, ExecutorClass=SExecutor
    ):
        self.solver = Solver()
        super().__init__(
            P, opts, executor or ExecutorClass(self.solver, opts)
        )
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler
        self._input_vector = None

    def set_input_vector(self, ivec):
        self._executor.set_input_vector(ivec)

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
        opts = self.getOptions()
        stats = self.stats
        if opts.replay_errors and s.hasError():
            print_stdout("Found an error, trying to replay it", color="white")
            repls = self.replay_state(s)
            if not repls or not repls.hasError():
                print_stderr("Failed replaying error", color="orange")
                s.setKilled("Failed replaying error")
            else:
                dbg("The replay succeeded.")

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
            if opts.exit_on_error:
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

    def replay_state(self, state):
        ivec = state.input_vector()
        dbg(f"Input vector: {ivec}")

        class GatherStates:
            class Handler:
                def __init__(self):
                    self.states = []

                def processState(self, s):
                    self.states.append(s)

            def __init__(self):
                self.testgen = GatherStates.Handler()
                self.states = self.testgen.states

        opts = SEOptions(self.getOptions())
        opts.replay_errors = False
        handler = GatherStates()
        SE = SymbolicExecutor(self.getProgram(),
                              handler,
                              opts)
        SE.set_input_vector(ivec)
        SE.run()
        if len(handler.states) != 1:
            return None
        return handler.states[0]

