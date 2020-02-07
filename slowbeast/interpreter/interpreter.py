from .. util.debugging import print_stderr, dbg
from . executionstate import ExecutionState
from . executor import Executor
from . errors import ExecutionError
from . interactive import InteractiveHandler

# dummy class used as a program counter during initialization
# of global variables


class GlobalInit:
    def getNextInstruction(self):
        return self


class Interpreter:
    def __init__(self, program, executor=Executor(), by_blocks=False, interactive=None):
        self._program = program
        self._executor = executor
        self._interactive = InteractiveHandler(self) if interactive else None
        self._execute_by_blocks = by_blocks

        self.entry = program.getEntry()
        self.states = []

    def getStates(self):
        return self.states

    def getInitialStates(self):
        """
        Get state(s) from which to start execution.
        May be overriden by child classes
        """
        return [ExecutionState(None)]

    def getNextState(self):
        if not self.states:
            return None

        # this is concrete execution
        assert len(self.states) == 1
        s = self.states.pop()
        assert len(self.states) == 0
        return s

    def handleNewStates(self, newstates):
        assert len(newstates) == 1,\
            "Concrete execution returned more than one state"

        state = newstates[0]
        if state.isReady():
            assert(len(self.states) == 0)
            self.states.append(state)
        elif state.hasError():
            print_stderr("Error while executing '{0}'".format(state),
                         color='RED')
            print_stderr(state.getError(), color='BROWN')
            state.dump()
        elif s.isTerminated():
            print_stderr(s.getError(), color='BROWN')
        elif s.wasKilled():
            print_stderr(
                s.getStatusDetail(),
                prefix='KILLED STATE: ',
                color='WINE')
        else:
            assert s.exited()
            dbg("state exited with exitcode {0}".format(s.getExitCode()))

        raise RuntimeError("This line should be unreachable")

    def interact_if_needed(self, s, newstates):
        if self._interactive is None:
            return

        self._interactive.prompt(s, newstates)

    def run_static(self):
        """ Run static ctors (e.g. initialize globals) """
        # fake the program counter for the executor
        ginit = GlobalInit()
        for s in self.states:
            s.pc = ginit

        for G in self._program.getGlobals():
            # bind the global to the state
            for s in self.states:
                s.bindGlobal(G, s.memory.allocateGlobal(G))

            if not G.hasInit():
                continue
            for i in G.getInit():
                for s in self.states:
                    ret = self._executor.execute(s, i)
                    assert len(ret) == 1, "Unhandled initialization"
                    assert ret[0] is s, "Unhandled initialization instruction"
                    assert ret[0].isReady(), "Generated errorneous state during initialization of globals"

    def run(self):
        self.states = self.getInitialStates()

        self.run_static()

        # push call to main to call stack
        for s in self.states:
            s.pushCall(None, self.entry)

        # we're ready to go!
        newstates = []
        try:
            while self.states:
                state = self.getNextState()
                self.interact_if_needed(state, newstates)
                if self._execute_by_blocks:
                    newstates = self._executor.executeTillBranch(state)
                else:
                    newstates = self._executor.execute(state, state.pc)
                self.handleNewStates(newstates)
        except ExecutionError as e:
            print_stderr(
                "Fatal error while executing '{0}': {1}".format(
                    state.pc, str(e)), color='RED')
            state.dump()
            return -1
        except Exception as e:
            print_stderr("Fatal error while executing '{0}'".format(state.pc),
                         color='RED')
            state.dump()
            raise e

        return 0
