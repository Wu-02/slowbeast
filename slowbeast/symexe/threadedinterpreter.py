from typing import Union

from slowbeast.core.errors import GenericError
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import Alloc, Call, Load, Store, ThreadJoin, Thread
from slowbeast.symexe.interpreter import SymbolicInterpreter
from slowbeast.symexe.options import SEOptions
from slowbeast.symexe.threadedexecutor import ThreadedExecutor
from slowbeast.util.debugging import print_stderr


# def is_same_mem(state, mem1, mem2, bytes_num):
#     p1 = state.eval(mem1)
#     p2 = state.eval(mem2)
#     if p1.is_concrete() and p2.is_concrete():
#         # FIXME: compare also offsets
#         return p1.object() == p2.object()
#     # TODO: fork?
#     return True
#
#
# def is_same_val(state, op1, op2):
#     """Return if True if reading mem1 and mem2 must result in the same value"""
#     val1 = state.try_eval(op1)
#     val2 = state.try_eval(op2)
#     if val1 is None or val2 is None:
#         return False
#     return val1 == val2
#
#
# def reads_same_val(state, loadop, storevalop, bytes_num):
#     p1 = state.eval(loadop)
#     val = state.try_eval(storevalop)
#     if val is None:
#         return False
#     lval, err = state.memory.read(p1, bytes_num)
#     if err:
#         return False
#     # TODO: handle symbolic values?
#     return lval == val
#
#
# def get_conflicting(state, thr):
#     "Get threads that will conflict with 'thr' if executed"
#     confl = []
#     pc = state.thread(thr).pc
#     isload, iswrite = isinstance(pc, Load), isinstance(pc, Store)
#     if not isload and not iswrite:
#         return confl
#     bytes_num = pc.bytewidth()
#     for idx, t in enumerate(state.threads()):
#         if idx == thr:
#             continue
#         tpc = t.pc
#         # we handle this differently
#         # if isinstance(tpc, Return) and idx == 0:
#         #    # return from main is always conflicting
#         #    confl.append(idx)
#         if isload and isinstance(tpc, Store):
#             if is_same_mem(state, pc.operand(0), tpc.operand(1), bytes_num):
#                 if not reads_same_val(state, pc.operand(0), tpc.operand(0), bytes_num):
#                     confl.append(idx)
#         elif iswrite:
#             if isinstance(tpc, Store):
#                 if is_same_mem(state, pc.operand(1), tpc.operand(1), bytes_num):
#                     if not is_same_val(state, pc.operand(0), tpc.operand(0)):
#                         confl.append(idx)
#             elif isinstance(tpc, Load):
#                 if is_same_mem(state, pc.operand(1), tpc.operand(0), bytes_num):
#                     confl.append(idx)
#     return confl
#


def may_be_glob_mem(state, mem: Alloc) -> bool:
    if isinstance(mem, Alloc):
        return False
    ptr = state.try_eval(mem)
    if ptr and ptr.object().is_concrete():
        mo = state.memory.get_obj(ptr.object().value())
        if mo and isinstance(mo.allocation(), Alloc):
            return False
    return True


def _is_global_event_fun(fn) -> bool:
    # FIXME: what if another thread is writing to arguments of pthread_create?
    # return name.startswith("pthread_")  or
    # name.startswith("__VERIFIER_atomic")
    name = fn.name()
    if name.startswith("__VERIFIER_atomic"):
        return True
    if fn.is_undefined() and name in (
        "pthread_mutex_lock",
        "pthread_mutex_unlock",
    ):
        return True
    return False


class ThreadedSymbolicInterpreter(SymbolicInterpreter):
    def __init__(self, P, ohandler=None, opts: SEOptions = SEOptions()) -> None:
        super().__init__(P, ohandler, opts, ExecutorClass=ThreadedExecutor)

    def _is_global_event(self, state, pc: Union[Call, Load, Store, ThreadJoin]) -> bool:
        if isinstance(pc, Load):
            return may_be_glob_mem(state, pc.operand(0))
        if isinstance(pc, Store):
            return may_be_glob_mem(state, pc.operand(1))
        if isinstance(pc, (Thread, ThreadJoin)):
            return True
        if isinstance(pc, Call):
            fn = pc.called_function()
            if not isinstance(fn, Function):
                fun = state.try_eval(fn)
                if fun is None:
                    return True
                fn = self.executor()._resolve_function_pointer(state, fun)
                if fn is None:
                    return True
                assert isinstance(fn, Function)
            return _is_global_event_fun(fn)
        return False

    def schedule(self, state):
        l = state.num_threads()
        if l == 0:
            return []
        # if the thread is in an atomic sequence, continue it...
        t = state.thread()
        if t.in_atomic():
            if not t.is_paused():
                return [state]
            # this thread is dead-locked, but other can continue
            state.set_killed(
                f"Thread {t.get_id()} is stucked "
                "(waits for a mutex inside an atomic sequence)"
            )
            return [state]

        is_global_ev = self._is_global_event
        for idx, t in enumerate(state.threads()):
            if t.is_paused():
                continue
            if not is_global_ev(state, t.pc):
                state.schedule(idx)
                return [state]

        can_run = [idx for idx, t in enumerate(state.threads()) if not t.is_paused()]
        if len(can_run) == 0:
            state.set_error(GenericError("Deadlock detected"))
            return [state]
        if len(can_run) == 1:
            state.schedule(can_run[0])
            return [state]

        states = []
        for idx in can_run:
            s = state.copy()
            s.schedule(idx)
            states.append(s)
        assert states
        return states

    def prepare(self) -> None:
        """
        Prepare the interpreter for execution.
        I.e. initialize static memory and push the call to
        the main function to call stack.
        Result is a set of states before starting executing
        the entry function.
        """
        self.states = self.initial_states()
        self.run_static()

        # push call to main to call stack
        entry = self.get_program().entry()
        for s in self.states:
            main_args = self._main_args(s)
            s.push_call(None, entry, args_mapping=main_args)
            assert s.num_threads() == 1
            s.sync_pc()

    def run(self) -> int:
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
                        for ns in newstates:
                            ns.sync_pc()
                    else:
                        newstates.append(s)

                # self.states_num += len(newstates)
                # if self.states_num % 100 == 0:
                #    print("Searched states: {0}".format(self.states_num))
                self.handle_new_states(newstates)
        except Exception as e:
            print_stderr(f"Fatal error while executing '{state.pc}'", color="red")
            state.dump()
            raise e

        self.report()

        return 0


def events_conflict(events, othevents) -> bool:
    for ev in (
        e
        for e in events
        if not e.is_call_of(("__VERIFIER_atomic_begin", "__VERIFIER_atomic_end"))
    ):
        for oev in (
            e
            for e in othevents
            if not e.is_call_of(("__VERIFIER_atomic_begin", "__VERIFIER_atomic_end"))
        ):
            if ev.conflicts(oev):
                return True
    return False


def has_conflicts(state, events, states_with_events) -> bool:
    for _, othstate, othevents in states_with_events:
        if state is othstate:
            continue
        if events_conflict(events, othevents):
            return True
    return False


class ThreadedDPORSymbolicExecutor(ThreadedSymbolicInterpreter):
    def __init__(self, P, ohandler=None, opts: SEOptions = SEOptions()) -> None:
        super().__init__(P, ohandler, opts)
        print("Running symbolic execution with DPOR")

    def _schedule_atomic(self, state) -> bool:
        assert state.num_threads() > 0
        # if the thread is in an atomic sequence, continue it...
        t = state.thread()
        if t.in_atomic():
            if not t.is_paused():
                return True
            # this thread is dead-locked, but other can continue
            state.set_killed(
                f"Thread {t.get_id()} is stucked "
                "(waits for a mutex inside an atomic sequence)"
            )
            return False

        is_global_ev = self._is_global_event
        for idx, t in enumerate(state.threads()):
            if t.is_paused():
                continue
            if not is_global_ev(state, t.pc):
                state.schedule(idx)
                return True
        return False

    def step(self, state):
        # execute a step and then finish any atomic/non-global events that
        # follow
        assert state.is_ready()
        queue, states = [], []
        execute = self._executor.execute
        is_global_ev = self._is_global_event
        if is_global_ev(state, state.pc):
            state.add_event()
        tmp = execute(state, state.pc)
        for ns in tmp:
            ns.sync_pc()
            (queue, states)[0 if ns.is_ready() else 1].append(ns)

        sched_atomic = self._schedule_atomic
        while queue:
            newq = []
            for s in queue:
                if sched_atomic(state):
                    if is_global_ev(s, s.pc):
                        s.add_event()
                    tmp = execute(s, s.pc)
                    for ns in tmp:
                        ns.sync_pc()
                        (newq, states)[0 if ns.is_ready() else 1].append(ns)
                else:
                    states.append(s)
            queue = newq
        return states

    def step_thread(self, state, idx):
        # execute a step and then finish any atomic/non-global events that
        # follow
        assert state.is_ready()
        queue, states = [], []
        execute = self._executor.execute
        is_global_ev = self._is_global_event
        state.schedule(idx)
        if is_global_ev(state, state.pc):
            state.add_event()
        tmp = execute(state, state.pc)
        for ns in tmp:
            ns.sync_pc()
            (queue, states)[0 if ns.is_ready() else 1].append(ns)

        is_global_ev = self._is_global_event
        while queue:
            newq = []
            for s in queue:
                assert s.num_threads() > 0
                t = s.thread()
                # if the thread is in an atomic sequence, continue it...
                if t.is_paused():
                    if t.in_atomic():
                        state.set_killed(
                            f"Thread {t.get_id()} is stucked "
                            "(waits for a mutex inside an atomic sequence)"
                        )
                    states.append(state)
                    continue
                if is_global_ev(s, s.pc):
                    if not t.in_atomic():
                        states.append(state)
                        continue
                    s.add_event()
                tmp = execute(s, s.pc)
                for ns in tmp:
                    ns.sync_pc()
                    (newq, states)[0 if ns.is_ready() else 1].append(ns)
            queue = newq
        return states

    def step_threads(self, state, tids):
        step_thread = self.step_thread
        ready, nonready = [state], []
        for tid in tids:
            newready = []
            for s in ready:
                idx = s._thread_idx(tid)
                assert idx is not None
                tmp = step_thread(s, idx)
                for ts in tmp:
                    (newready, nonready)[0 if ts.is_ready() else 1].append(ts)
            ready = newready
        return ready + nonready

    def run(self) -> int:
        self.prepare()

        # we're ready to go!
        state = None

        try:
            state = self._run()
        except Exception as e:
            print_stderr(
                f"Fatal error while executing '{state.pc if state else '<no state>'}'",
                color="red",
            )
            state.dump()
            raise e

        self.report()

        return 0

    def _run(self):
        get_next = self.get_next_state
        step = self.step
        step_thread = self.step_thread
        handle_new_states = self.handle_new_states
        while self.states:
            state = get_next()
            assert state.is_ready(), state.status()
            can_run = [
                idx for idx, t in enumerate(state.threads()) if not t.is_paused()
            ]
            if len(can_run) == 0:  # nothing to run
                state.set_error(GenericError("Deadlock detected"))
                newstates = [state]
            elif len(can_run) == 1:  # only one possible thread to run
                state.schedule(can_run[0])
                newstates = step(state)
            else:
                # more options, fork!
                newstates = []
                oldevs = state.events()
                ev = state.get_last_event()
                states_with_events = []
                # execute an event in each thread and gather all the new
                # states and events
                for idx in can_run:
                    s = state.copy()
                    tid = state.thread_id(idx)
                    tmp = step_thread(s, idx)
                    for ns in tmp:
                        if not ns.is_ready():
                            newstates.append(ns)
                            continue
                        events = ns.events()
                        assert events[len(oldevs) - 1] is ev
                        states_with_events.append((tid, ns, events[len(oldevs) :]))

                independent = set()
                for tid, ns, events in states_with_events:
                    if not has_conflicts(ns, events, states_with_events):
                        independent.add(tid)
                # move all independent threads
                if independent:
                    if len(independent) == len(states_with_events):
                        # if all threads did an independent event, pick one
                        # and move the others
                        independent.remove(states_with_events[0][0])
                        states_with_events = [states_with_events[0]]
                    for tid, ns, events in states_with_events:
                        if tid in independent:
                            continue
                        newstates += self.step_threads(ns, independent)
                else:
                    newstates += [s for _, s, _ in states_with_events]

            handle_new_states(newstates)
        return state
