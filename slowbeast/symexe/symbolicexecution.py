from slowbeast.interpreter.interpreter import Interpreter, ExecutionOptions
from slowbeast.solvers.solver import Solver
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from slowbeast.ir.instruction import Load, Store, Thread, ThreadJoin, Return, Alloc
from slowbeast.core.errors import GenericError
from .executor import Executor as SExecutor, ThreadedExecutor


class SEOptions(ExecutionOptions):
    def __init__(self, opts=None):
        super().__init__(opts)
        if opts:
            self.incremental_solving = opts.incremental_solving
            self.replay_errors = opts.replay_errors
            self.concretize_nondets = opts.concretize_nondets
            self.uninit_is_nondet = opts.uninit_is_nondet
            self.exit_on_error = opts.exit_on_error
            self.error_funs = opts.error_funs
            self.threads = opts.threads
        else:
            self.threads = False
            self.incremental_solving = False
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

    def add(self, rhs):
        self.paths = rhs.paths
        self.exited_paths = rhs.exited_paths
        self.killed_paths = rhs.killed_paths
        self.terminated_paths = rhs.terminated_paths
        self.errors = rhs.errors


class SymbolicExecutor(Interpreter):
    def __init__(
        self, P, ohandler=None, opts=SEOptions(), executor=None, ExecutorClass=SExecutor
    ):
        self._solver = Solver()
        super().__init__(P, opts, executor or ExecutorClass(self._solver, opts))
        self.stats = SEStats()
        # outputs handler
        self.ohandler = ohandler
        self._input_vector = None

    def set_input_vector(self, ivec):
        self._executor.set_input_vector(ivec)

    # FIXME: make this a method of output handler or some function (get rid of 'self')
    # after all, we want such functionality with every analysis
    def new_output_file(self, name):
        odir = self.ohandler.outdir if self.ohandler else None
        return open("{0}/{1}".format(odir or ".", name), "w")

    def solver(self):
        return self._solver

    def get_next_state(self):
        states = self.states
        if not states:
            return None

        # DFS for now
        return states.pop()

    def handle_new_states(self, newstates):
        hs = self.handle_new_state
        for s in newstates:
            hs(s)

    def handle_new_state(self, s):
        testgen = self.ohandler.testgen if self.ohandler else None
        opts = self.getOptions()
        stats = self.stats
        if s.has_error() and opts.replay_errors and not opts.threads:
            print_stdout("Found an error, trying to replay it", color="white")
            repls = self.replay_state(s)
            if not repls or not repls.has_error():
                print_stderr("Failed replaying error", color="orange")
                s.set_killed("Failed replaying error")
            else:
                dbg("The replay succeeded.")

        if s.is_ready():
            self.states.append(s)
        elif s.has_error():
            dbgloc = s.pc.get_metadata("dbgloc")
            if dbgloc:
                print_stderr(
                    f"[{s.get_id()}] {dbgloc[0]}:{dbgloc[1]}:{dbgloc[2]}: {s.get_error()}",
                    color="redul",
                )
            else:
                print_stderr(
                    "{0}: {1} @ {2}".format(s.get_id(), s.get_error(), s.pc),
                    color="redul",
                )
            print_stderr("Error found.", color="red")
            stats.errors += 1
            stats.paths += 1
            if testgen:
                testgen.processState(s)
            if opts.exit_on_error:
                dbg("Found an error, terminating the search.")
                self.states = []
                return
        elif s.is_terminated():
            print_stderr(s.get_error(), color="BROWN")
            stats.paths += 1
            stats.terminated_paths += 1
            if testgen:
                testgen.processState(s)
        elif s.was_killed():
            stats.paths += 1
            stats.killed_paths += 1
            print_stderr(s.status_detail(), prefix="KILLED STATE: ", color="WINE")
            if testgen:
                testgen.processState(s)
        else:
            assert s.exited()
            dbg("state exited with exitcode {0}".format(s.get_exit_code()))
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
        SE = SymbolicExecutor(self.getProgram(), handler, opts)
        SE.set_input_vector(ivec)
        SE.run()
        if len(handler.states) != 1:
            return None
        return handler.states[0]


def may_be_glob_mem(mem):
    if isinstance(mem, Alloc):
        return False
    return True


def is_global_ev(pc, ismain):
    if isinstance(pc, Load):
        return may_be_glob_mem(pc.operand(0))
    if isinstance(pc, Store):
        return may_be_glob_mem(pc.operand(1))
    return isinstance(pc, (Thread, ThreadJoin)) or (isinstance(pc, Return) and ismain)


def is_same_mem(state, mem1, mem2, bytesNum):
    p1 = state.eval(mem1)
    p2 = state.eval(mem2)
    if p1.is_concrete() and p2.is_concrete():
        # FIXME: compare also offsets
        return p1.object() == p2.object()
    # TODO: fork?
    return True


def is_same_val(state, op1, op2):
    """Return if True if reading mem1 and mem2 must result in the same value"""
    val1 = state.try_eval(op1)
    val2 = state.try_eval(op2)
    if val1 is None or val2 is None:
        return False
    return val1 == val2


def reads_same_val(state, loadop, storevalop, bytesNum):
    p1 = state.eval(loadop)
    val = state.try_eval(storevalop)
    if val is None:
        return False
    lval, err = state.memory.read(p1, bytesNum)
    if err:
        return False
    # TODO: handle symbolic values?
    return lval == val


def get_conflicting(state, thr):
    "Get threads that will conflict with 'thr' if executed"
    confl = []
    pc = state.thread(thr).pc
    isload, iswrite = isinstance(pc, Load), isinstance(pc, Store)
    if not isload and not iswrite:
        return confl
    bytesNum = pc.bytewidth()
    for idx, t in enumerate(state.threads()):
        if idx == thr:
            continue
        tpc = t.pc
        # we handle this differently
        # if isinstance(tpc, Return) and idx == 0:
        #    # return from main is always conflicting
        #    confl.append(idx)
        if isload and isinstance(tpc, Store):
            if is_same_mem(state, pc.operand(0), tpc.operand(1), bytesNum):
                if not reads_same_val(state, pc.operand(0), tpc.operand(0), bytesNum):
                    confl.append(idx)
        elif iswrite:
            if isinstance(tpc, Store):
                if is_same_mem(state, pc.operand(1), tpc.operand(1), bytesNum):
                    if not is_same_val(state, pc.operand(0), tpc.operand(0)):
                        confl.append(idx)
            elif isinstance(tpc, Load):
                if is_same_mem(state, pc.operand(1), tpc.operand(0), bytesNum):
                    confl.append(idx)
    return confl


class ThreadedSymbolicExecutor(SymbolicExecutor):
    def __init__(self, P, ohandler=None, opts=SEOptions()):
        super().__init__(P, ohandler, opts, ExecutorClass=ThreadedExecutor)

    def schedule(self, state):
        l = state.num_threads()
        assert l > 0
        # if the thread is in an atomic sequence, continue it...
        if state.thread().in_atomic():
            return [state]

        for idx, t in enumerate(state.threads()):
            if t.is_paused():
                continue
            if not is_global_ev(t.pc, t.get_id() == 0):
                state.schedule(idx)
                return [state]

        can_run = [idx for idx, t in enumerate(state.threads()) if not t.is_paused()]
        if len(can_run) == 1:
            state.schedule(can_run[0])
            return [state]
        else:
            states = []
            for idx in can_run:
                s = state.copy()
                s.schedule(idx)
                states.append(s)
            if not states:
                state.set_error(GenericError("Deadlock detected"))
                return [state]
            assert states
            return states

        # this is not CORRECT!

    # can_run = set(idx for idx, t in enumerate(state.threads()) if not t.is_paused())
    # if not can_run:
    #    state.set_error(GenericError("Deadlock detected"))
    #    return [state]

    # thr = can_run.pop()
    # if len(can_run) > 0 and thr == 0 and isinstance(state.thread(0).pc, Return):
    #    # defer scheduling the return from the main thread as the last possible event,
    #    # so that we do not try only partial executions
    #    # FIXME: this is incorrect if we are interested e.g., in memory leaks
    #    # if we get rid of this hack, we must return all threads as possibly conflicting
    #    # from 'get_conflicting' if thr == 0 and pc is a return
    #    thr = can_run.pop()
    # state.schedule(thr)
    # if len(can_run) == 0:
    #    return [state]
    # else:
    #    conflicting = get_conflicting(state, thr)
    #    if not conflicting:
    #        return [state]
    #    states = [state]
    #    for idx in conflicting:
    #        s = state.copy()
    #        s.schedule(idx)
    #        states.append(s)
    #    assert states
    #    return states

    def prepare(self):
        """
        Prepare the interpreter for execution.
        I.e. initialize static memory and push the call to
        the main function to call stack.
        Result is a set of states before starting executing
        the entry function.
        """
        self.states = self.initialStates()
        self.run_static()

        # push call to main to call stack
        entry = self.getProgram().entry()
        for s in self.states:
            main_args = self._main_args(s)
            s.push_call(None, entry, argsMapping=main_args)
            assert s.num_threads() == 1
            s.sync_pc()

    def run(self):
        self.prepare()

        # we're ready to go!
        schedule = self.schedule
        try:
            while self.states:
                newstates = []
                state = self.get_next_state()
                self.interact_if_needed(state)
                for s in schedule(state):
                    if s.is_ready():
                        newstates += self._executor.execute(s, s.pc)
                        s.sync_pc()
                    else:
                        newstates.append(s)

                # self.states_num += len(newstates)
                # if self.states_num % 100 == 0:
                #    print("Searched states: {0}".format(self.states_num))
                self.handle_new_states(newstates)
        except Exception as e:
            print_stderr(
                "Fatal error while executing '{0}'".format(state.pc), color="RED"
            )
            state.dump()
            raise e

        self.report()

        return 0
