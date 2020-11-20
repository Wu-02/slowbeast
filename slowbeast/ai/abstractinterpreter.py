from ..interpreter.interpreter import Interpreter
from slowbeast.symexe.symbolicexecution import SEOptions
from .executor import Executor as AIExecutor
from ..util.debugging import print_stderr, dbg


class AIOptions(SEOptions):
    pass


class AIStats:
    def __init__(self):
        # all paths (including ones that hit an error or terminated early)
        self.paths = 0
        # paths that exited (the state is exited)
        self.exited_paths = 0
        self.killed_paths = 0
        self.terminated_paths = 0
        self.errors = 0


class AbstractInterpreter(Interpreter):
    def __init__(
        self,
        P,
        ohandler=None,
        opts=AIOptions(),
        executor=None,
        ExecutorClass=AIExecutor,
    ):
        super().__init__(P, opts, executor or ExecutorClass(opts))
        self.stats = AIStats()
        # outputs handler
        self.ohandler = ohandler
        self.explored_states = {}

    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

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
        pc = s.pc
        if s in self.explored_states.setdefault(pc, set()):
            dbg("Already have this state")
            # if s.hasError():
            #    s.dump()
            #    print('---- HAVE ----')
            #    for x in self.explored_states[s.pc]:
            #        if x == s:
            #            x.dump()
            return
        self.explored_states[pc].add(s)

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

    def report(self):
        pass

    # expl = self.explored_states
    # for pc, S in expl.items():
    #    pc.dump()
    #    print(' --- states ---')
    #    for s in S:
    #        s.dump()
    #    print(' --- all states ---')
