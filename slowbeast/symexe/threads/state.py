from sys import stdout
from typing import Union, Optional, List, TextIO

from slowbeast.core.callstack import CallStack
from slowbeast.core.state import ExecutionState
from slowbeast.ir.instruction import Alloc, GlobalVariable, ThreadJoin
from slowbeast.symexe.state import SEState as BaseState, Thread, Event
from slowbeast.util.debugging import ldbgv


class TSEState(BaseState):
    __slots__ = (
        "_threads",
        "_current_thread",
        "_exited_threads",
        "_wait_join",
        "_wait_mutex",
        "_mutexes",
        "_last_tid",
        # "_trace",
        "_event_trace",
        "_events",
        "_conflicts",
    )

    def __init__(
        self, executor=None, pc=None, m=None, solver=None, constraints=None
    ) -> None:
        super().__init__(executor, pc, m, solver, constraints)
        self._last_tid = 0
        self._current_thread = 0
        self._threads = [Thread(0, pc, self.memory.get_cs() if m else None)]
        # threads waiting in join until the joined thread exits
        self._wait_join = {}
        self._exited_threads = {}
        self._event_trace = []
        # self._trace = []
        self._events = []  # the sequence of events (for DPOR)
        self._mutexes = {}
        self._wait_mutex = {}
        self._conflicts = []

    def _thread_idx(self, thr: Thread) -> int:
        if isinstance(thr, Thread):
            return self._threads.index(thr)
        for idx, t in enumerate(self._threads):
            if t.get_id() == thr:
                return idx
        return None

    def _copy_to(self, new: ExecutionState) -> None:
        super()._copy_to(new)
        new._threads = [t.copy() for t in self._threads]
        new._wait_join = self._wait_join.copy()
        new._exited_threads = self._exited_threads.copy()
        new._last_tid = self._last_tid
        new._current_thread = self._current_thread
        # new._trace = self._trace.copy()
        new._event_trace = self._event_trace.copy()
        new._events = self._events.copy()
        new._conflicts = self._conflicts.copy()
        # FIXME: do COW (also for wait and exited threads ...)
        new._mutexes = self._mutexes.copy()
        new._wait_mutex = {mtx: W.copy() for mtx, W in self._wait_mutex.items() if W}

    def trace(self):
        return self._event_trace

    def lazy_eval(self, v: Union[Alloc, GlobalVariable]):
        value = self.try_eval(v)
        if value is None:
            vtype = v.type()
            if vtype.is_pointer():
                if isinstance(
                    v, (Alloc, GlobalVariable)
                ):  # FIXME: this is hack, do it generally for pointers
                    self.executor().memorymodel.lazy_allocate(self, v)
                    return self.try_eval(v)
                name = f"unknown_ptr_{v.as_value()}"
            else:
                name = f"unknown_{v.as_value()}"
            value = self.solver().symbolic_value(name, v.type())
            ldbgv(
                "Created new nondet value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.create_nondet(v, value)
        return value

    def sync_pc(self) -> None:
        if self._threads:
            self._threads[self._current_thread].pc = self.pc

    def add_event(self) -> None:
        self._events.append(Event(self))

    def get_last_event(self):
        if self._events:
            return self._events[-1]
        return None

    def events(self):
        return self._events

    def schedule(self, idx: int) -> None:
        if self._current_thread == idx:
            return
        assert idx < len(self._threads)
        # sync current thread
        thr = self._threads[self._current_thread]
        thr.pc, thr.cs = self.pc, self.memory.get_cs()

        # schedule new thread
        thr: Thread = self._threads[idx]
        assert thr, self._threads
        self.pc = thr.pc
        self.memory.set_cs(thr.cs)
        self._current_thread = idx

        self._event_trace.append((self.thread_id(), self.pc))

    def add_thread(self, thread_fn, pc, args) -> Thread:
        self._last_tid += 1
        cs = CallStack()
        cs.push_call(None, thread_fn, args)
        t = Thread(self._last_tid, pc, cs)
        assert not t.is_paused()
        self._threads.append(t)
        # self._trace.append(f"add thread {t.get_id()}")
        return t

    def current_thread(self) -> int:
        return self._current_thread

    def thread(self, idx=None) -> Thread:
        return self._threads[self._current_thread if idx is None else idx]

    def thread_id(self, idx=None):
        return self._threads[self._current_thread if idx is None else idx].get_id()

    def pause_thread(self, idx=None) -> None:
        # self._trace.append(f"pause thread {self.thread(idx).get_id()}")
        self._threads[self._current_thread if idx is None else idx].pause()

    def unpause_thread(self, idx=None) -> None:
        # self._trace.append(f"unpause thread {self.thread(idx).get_id()}")
        self._threads[self._current_thread if idx is None else idx].unpause()

    def start_atomic(self, idx=None) -> None:
        # self._trace.append(f"thread {self.thread(idx).get_id()} begins atomic sequence")
        assert not self._threads[
            self._current_thread if idx is None else idx
        ].in_atomic()
        self._threads[self._current_thread if idx is None else idx].set_atomic(True)

    def end_atomic(self, idx=None) -> None:
        # self._trace.append(f"thread {self.thread(idx).get_id()} ends atomic sequence")
        assert self._threads[self._current_thread if idx is None else idx].in_atomic()
        self._threads[self._current_thread if idx is None else idx].set_atomic(False)

    def mutex_locked_by(self, mtx):
        return self._mutexes.get(mtx)

    def mutex_init(self, mtx) -> None:
        self._mutexes[mtx] = None

    def mutex_destroy(self, mtx) -> None:
        self._mutexes.pop(mtx)

    def has_mutex(self, mtx):
        return mtx in self._mutexes

    def mutex_lock(self, mtx, idx=None) -> None:
        # self._trace.append(f"thread {self.thread(idx).get_id()} locks mutex {mtx}")
        tid = self.thread(self._current_thread if idx is None else idx).get_id()
        assert self.mutex_locked_by(mtx) is None, "Locking locked mutex"
        self._mutexes[mtx] = tid

    def mutex_unlock(self, mtx, idx=None) -> None:
        # self._trace.append(f"thread {self.thread(idx).get_id()} unlocks mutex {mtx}")
        assert (
            self.mutex_locked_by(mtx)
            == self.thread(self._current_thread if idx is None else idx).get_id()
        ), "Unlocking wrong mutex"
        self._mutexes[mtx] = None
        tidx = self._thread_idx
        unpause = self.unpause_thread
        W = self._wait_mutex.get(mtx)
        if W is not None:
            for tid in W:
                unpause(tidx(tid))
            self._wait_mutex[mtx] = set()

    def mutex_wait(self, mtx, idx=None) -> None:
        "Thread idx waits for mutex mtx"

        # self._trace.append(f"thread {self.thread(idx).get_id()} waits for mutex {mtx}")
        tid = self._current_thread if idx is None else idx
        assert self.mutex_locked_by(mtx) is not None, "Waiting for unlocked mutex"
        self.pause_thread(idx)
        self._wait_mutex.setdefault(mtx, set()).add(self.thread(tid).get_id())

    def exit_thread(self, retval, tid: Optional[Thread] = None) -> None:
        """Exit thread and wait for join (if not detached)"""
        if tid is None:
            tid = self.thread().get_id()
        # self._trace.append(f"exit thread {tid} with val {retval}")
        assert tid not in self._exited_threads
        self._exited_threads[tid] = retval
        tidx = self._thread_idx(tid)
        self.remove_thread(tidx)

        if tid in self._wait_join:
            # self._trace.append(f"thread {tid} was waited for by {self._wait_join[tid]}")
            # idx of the thread that is waiting on 'tid' to exit
            waitidx = self._thread_idx(self._wait_join[tid])
            assert self.thread(waitidx).is_paused(), self._wait_join
            self.unpause_thread(waitidx)
            t = self.thread(waitidx)
            # pass the return value
            assert isinstance(t.pc, ThreadJoin), t
            t.cs.set(t.pc, retval)
            t.pc = t.pc.get_next_inst()
            self._wait_join.pop(tid)

    def join_threads(self, tid, totid: Optional[Thread] = None) -> None:
        """
        tid: id of the thread to join
        totid: id of the thread to which to join (None means the current thread)
        """
        # self._trace.append(
        #    f"join thread {tid} to {self.thread().get_id() if totid is None else totid}"
        # )
        if tid in self._exited_threads:
            # pass the return value
            retval = self._exited_threads.pop(tid)
            self.set(self.pc, retval)
            self.pc = self.pc.get_next_inst()
            # self._trace.append(
            #    f"thread {tid} waited for a join, joining with val {retval}"
            # )
            return

        assert tid not in self._wait_join, f"{tid} :: {self._wait_join}"
        if totid is None:
            # self._trace.append(
            #    f"thread {tid} is waited in join by {self.thread().get_id()}"
            # )
            self._wait_join[tid] = self.thread().get_id()
            toidx = self._current_thread
        else:
            # self._trace.append(f"thread {tid} is waited in join by {totid}")
            self._wait_join[tid] = totid
            toidx = self._thread_idx(totid)
        self.pause_thread(toidx)

    def remove_thread(self, idx=None) -> None:
        # self._trace.append(f"removing thread {self.thread(idx).get_id()}")
        self._threads.pop(self._current_thread if idx is None else idx)
        # schedule thread 0 (if there is any) -- user will reschedule if
        # desired
        if self._threads:
            self.pc = self._threads[0].pc
            self.memory.set_cs(self._threads[0].cs)
            self._current_thread = 0

        # after the last thread terminates, exit(0) is called
        # see man pthread_exit
        if self.num_threads() == 0:
            self.set_exited(0)

    def num_threads(self) -> int:
        return len(self._threads)

    def threads(self) -> List[Thread]:
        return self._threads

    def add_conflict(self, state) -> None:
        self._conflicts.append((state.get_last_event(), state))

    def filter_conflicts(self, ev=None):
        if ev is None:
            ev = self.get_last_event()
        ret, newc = [], []
        conflicts = ev.conflicts
        for cev, s in self._conflicts:
            if conflicts(cev):
                ret.append(s)
            else:
                newc.append((cev, s))
        self._conflicts = newc
        return ret

    def dump(self, stream: TextIO = stdout) -> None:
        super().dump(stream)
        write = stream.write
        write(" -- Threads --\n")
        for idx, t in enumerate(self._threads):
            write(f"  {idx}: {t}\n")

        write(f" -- Exited threads waiting for join: {self._exited_threads}\n")
        write(f" -- Threads waiting in join: {self._wait_join}\n")
        write(f" -- Mutexes (locked by): {self._mutexes}\n")
        write(f" -- Threads waiting for mutexes: {self._wait_mutex}\n")
        write(" -- Events --\n")
        for it in self._events:
            write(str(it) + "\n")

    # write(" -- Trace --\n")
    # for it in self._trace:
    #    write(it + "\n")
