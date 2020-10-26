from ..interpreter.interpreter import Interpreter, ExecutionOptions
from .executor import Executor as SExecutor
from .memory import SymbolicMemoryModel
from ..solvers.solver import Solver
from ..util.debugging import print_stderr, print_stdout, dbg


class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super(SEOptions, self).__init__(opts)
        if opts:
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
        else:
            self.concretize_nondets = False
            self.uninit_is_nondet = False
            self.exit_on_error = False


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
        super(SymbolicExecutor, self).__init__(
            P, opts, executor or ExecutorClass(self.solver, opts)
        )
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler

    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

    def getSolver(self):
        return self.solver

    def getNextState(self):
        if not self.states:
            return None

        # DFS for now
        return self.states.pop()

    def handleNewStates(self, newstates):
        testgen = self.ohandler.testgen if self.ohandler else None
        for s in newstates:
            if s.isReady():
                self.states.append(s)
            elif s.hasError():
                print_stderr(
                    "{0}: {1}, {2}".format(s.getID(), s.pc, s.getError()), color="RED"
                )
                self.stats.errors += 1
                self.stats.paths += 1
                if testgen:
                    testgen.processState(s)
                if self.getOptions().exit_on_error:
                    dbg("Found an error, terminating the search.")
                    self.states = []
                    return
            elif s.isTerminated():
                print_stderr(s.getError(), color="BROWN")
                self.stats.paths += 1
                self.stats.terminated_paths += 1
                if testgen:
                    testgen.processState(s)
            elif s.wasKilled():
                self.stats.paths += 1
                self.stats.killed_paths += 1
                print_stderr(s.getStatusDetail(), prefix="KILLED STATE: ", color="WINE")
                if testgen:
                    testgen.processState(s)
            else:
                assert s.exited()
                dbg("state exited with exitcode {0}".format(s.getExitCode()))
                self.stats.paths += 1
                self.stats.exited_paths += 1
                if testgen:
                    testgen.processState(s)
