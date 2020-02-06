from .. util.debugging import print_stderr, dbg
from . executionstate import ExecutionState
from . executor import Executor
from . errors import ExecutionError


class InteractiveHandler:
    def __init__(self, interpreter):
        self.interpreter = interpreter
        self._last_query = None
        self._stop_next_time = True
        self._break_inst = []
        self._break_pathid = []

    # a helper wrapper for _id do to look-up in memory
    # (this is a bit of a hack...)
    class DummyValue:
        def __init__(self, _id):
            self._id = _id

    def _shouldSkip(self, s, newstates):
        if self._stop_next_time:
            return False
        if s.getID() in self._break_pathid:
            return False
        if s.pc.getID() in self._break_inst:
            return False
        return True

    def prompt(self, s, newstates):
        """ s = currently executed state
            newstates = states generated
        """
        try:
            return self._prompt(s, newstates)
        except EOFError:
            from sys import exit
            print("Exiting...")
            exit(0)

    def _prompt(self, s, newstates):
        if self._shouldSkip(s, newstates):
            return

        self._stop_next_time = False

        print(
            "Stopped before executing: ({0}) {1}".format(
                s.getID(), str(
                    s.pc)))
        q = input("> ")
        if q == '':
            q = self._last_query
        while not self.handle(q, s, newstates):
            q = input("> ")

        self._last_query = q

    def handle(self, q, s, newstates):
        """ Return False for new prompt (the handling was unsuccessful) """
        try:
            return self._handle(q, s, newstates)
        except KeyboardInterrupt:
            print("Interrupted")
            return False
        except Exception as e:
            print("An exception occured during handling '{0}'".format(q))
            print(str(e))
            return False
        return False

    def _handle(self, q, s, newstates):
        dbg('query: {0}'.format(q))
        query = q.split()
        if len(query) < 1:
            return False

        if query[0] in ['c', 'continue']:
            return True  # True = continute
        if query[0] in ['n', 's', 'step', 'next']:
            self._stop_next_time = True
            return True
        elif query[0] == 'p':
            self.handlePrint(query[1:], s, newstates)
        elif query[0] == 'b':
            self.handleBreak(query[1:], s, newstates)
        elif query[0] in ['l', 'list']:
            if len(query) == 1:
                i = s.pc
                n = 0
                while i and n < 5:
                    i.dump()
                    i = i.getNextInstruction()
                    n += 1
            elif query[1] in ['b', 'bblock', 'block']:
                s.pc.getBBlock().dump()
        else:
            print("Unknown query: {0}".format(q))
            print("FIXME: ... print help ...")
        return False

    def _getstate(self, i):
        for s in self.interpreter.getStates():
            if s.getID() == i:
                return s
        return None

    def handleBreak(self, query, state, newstates):
        if not query:
            print("Break on instructions: ", self._break_inst)
            print("Break on path ID: ", self._break_pathid)
        if query[0] in ['p', 'path']:
            self._break_pathid.append(int(query[1]))
            print("Break on path ID: ", self._break_pathid)
        elif query[0] in ['i', 'inst', 'instruction']:
            self._break_inst.append(int(query[1]))
            print("Break on instructions: ", self._break_inst)
        # elif query[0] in ['s', 'state']: # XXX: states do not have any unique
        # id (yet?)...

    def handlePrint(self, query, state, newstates):
        if not query:
            raise RuntimeError("Invalid arguments to print")
        if query[0] == 'states':
            print([x.getID() for x in self.interpreter.getStates()])
        elif query[0] in ['new', 'newstates']:
            print([x.getID() for x in self.interpreter.getStates()])
        elif query[0] in ['s', 'state']:
            if len(query) == 1:
                assert state, "No current state"
                s = state
            else:
                s = self._getstate(int(query[1]))
            if s:
                s.dump()
            else:
                print('No such a state')
        # elif query[0].startswith('x'):
           # FIXME need to get the Instruction first
           # if val is None:
           #    print("No such a value")
           # else:
           #    print("{0} -> {1}".format(query[0], val))
        else:
            raise NotImplementedError("Invalid print command")

# dummy class used as a program counter during initialization
# of global variables


class GlobalInit:
    def getNextInstruction(self):
        return self


class Interpreter:
    def __init__(self, program, executor=Executor(), interactive=None):
        self._program = program
        self._executor = executor
        self._interactive = InteractiveHandler(self) if interactive else None

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
                s.dump()

            if not G.hasInit():
                continue
            for i in G.getInit():
                for s in self.states:
                    ret = self._executor.execute(s, i)
                    assert len(ret) == 1, "Unhandled initialization"
                    assert ret[0] is s, "Unhandled initialization instruction"

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
