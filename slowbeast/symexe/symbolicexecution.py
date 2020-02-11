from .. interpreter.interpreter import Interpreter, ExecutionOptions
from .. interpreter.errors import ExecutionError
from . executor import Executor as SExecutor
from . executionstate import SEState
from . memory import SymbolicMemory
from .. solvers.solver import Solver
from .. util.debugging import print_stderr, print_stdout, dbg

class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super(SEOptions, self).__init__(opts)
        if opts:
            self.concretize_nondets = opts.concretize_nondets
        else:
            self.concretize_nondets = False

class Stats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0
        self.instructions = 0


class SymbolicExecutor(Interpreter):
    def __init__(
            self,
            P,
            testgen=None,
            opts=SEOptions()):
        self.solver = Solver()
        super(
            SymbolicExecutor,
            self).__init__(
            P,
            opts,
            SExecutor(opts))
        self.stats = Stats()
        self.testgen = testgen

    def getSolver(self):
        return self.solver

    def getInitialStates(self):
        return [SEState(None, SymbolicMemory(self.solver), self.solver)]

    def getNextState(self):
        if not self.states:
            return None

        # DFS for now
        return self.states.pop()

    def handleNewStates(self, newstates):
        self.stats.instructions += 1
        for s in newstates:
            if s.isReady():
                self.states.append(s)
            elif s.hasError():
                print_stderr(
                    "{0}: {1}, {2}".format(
                        s.getID(),
                        s.pc,
                        s.getError()),
                    color='RED')
                self.stats.errors += 1
                self.stats.paths += 1
                if self.testgen:
                    self.testgen.processState(s)
            elif s.isTerminated():
                print_stderr(s.getError(), color='BROWN')
                self.stats.paths += 1
                self.stats.terminated_paths += 1
                if self.testgen:
                    self.testgen.processState(s)
            elif s.wasKilled():
                self.stats.paths += 1
                self.stats.killed_paths += 1
                print_stderr(
                    s.getStatusDetail(),
                    prefix='KILLED STATE: ',
                    color='WINE')
                if self.testgen:
                    self.testgen.processState(s)
            else:
                assert s.exited()
                dbg("state exited with exitcode {0}".format(s.getExitCode()))
                self.stats.paths += 1
                self.stats.exited_paths += 1
                if self.testgen:
                    self.testgen.processState(s)
