from .. interpreter.interpreter import Interpreter
from .. interpreter.errors import ExecutionError
from . executor import Executor as SExecutor
from . executionstate import SEState
from .. solvers.solver import Solver
from .. util.debugging import print_stderr, print_stdout, dbg


class Stats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.errors = 0
        self.instructions = 0


class SymbolicExecutor(Interpreter):
    def __init__(self, P):
        self.solver = Solver()
        super(SymbolicExecutor, self).__init__(P, SExecutor(self.solver))

        self.stats = Stats()

    def getInitialStates(self, entry):
        s = SEState()
        s.pushCall(None, entry)
        return [s]

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
                print_stderr(s.getError(), color='RED')
                self.stats.errors += 1
                self.stats.paths += 1
            elif s.isTerminated():
                print_stderr(s.getError(), color='BROWN')
                self.stats.paths += 1
            else:
                assert s.exited()
                dbg("state exited with exitcode {0}".format(s.getExitCode()))
                self.stats.paths += 1
                self.stats.exited_paths += 1

    def run(self):
        self.states = self.getInitialStates(self.entry)

        try:
            while self.states:
                state = self.getNextState()
                newstates = self._executor.execute(state, state.pc)
                self.handleNewStates(newstates)
        except ExecutionError as e:
            print_stderr(
                "Execution error while executing '{0}': {1}".format(
                    state, str(e)), color='RED')
            state.dump()
            return -1
        except Exception as e:
            print_stderr("Fatal error while executing '{0}'".format(state.pc),
                         color='RED')
            state.dump()
            raise e

        print_stdout(
            "Executed instructions: {0}".format(
                self.stats.instructions),
            color='CYAN')
        print_stdout(
            "Executed paths: {0}".format(
                self.stats.paths),
            color='CYAN')
        print_stdout(
            "Paths that reached exit: {0}".format(
                self.stats.exited_paths),
            color='CYAN')
        print_stdout(
            "Executed branch instructions: {0}".format(
                self._executor.stats.branchings),
            color='CYAN')
        print_stdout(
            "Number of forks on branches: {0} (forked on {1}% of branches)".format(
                self._executor.stats.branch_forks,
                100*float(self._executor.stats.branch_forks) / self._executor.stats.branchings),
            color='CYAN')
        # this includes e.g. forks on assertions/memory resolution/etc.
        print_stdout(
            "Number of all forks: {0} (from {1} calls ({2}%) to fork())".format(self._executor.stats.forks, self._executor.stats.fork_calls,
                100*float(self._executor.stats.forks) / self._executor.stats.fork_calls),
            color='CYAN')
        print_stdout(
            "Found errors: {0}".format(
                self.stats.errors),
            color='CYAN')

        return 0
