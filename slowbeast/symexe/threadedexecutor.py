from typing import Optional

from slowbeast.core.errors import GenericError
from slowbeast.domains.concrete import concrete_value
from slowbeast.ir.instruction import ThreadJoin, Return, Thread
from slowbeast.ir.types import get_offset_type
from slowbeast.symexe.state import ThreadedSEState
from slowbeast.symexe.iexecutor import IExecutor
from slowbeast.symexe.memorymodel import SymbolicMemoryModel
from slowbeast.util.debugging import ldbgv, dbgv


class ThreadedExecutor(IExecutor):
    def __init__(
        self, program, solver, opts, memorymodel: Optional[SymbolicMemoryModel] = None
    ) -> None:
        super().__init__(program, solver, opts, memorymodel)

    def create_state(self, pc=None, m=None) -> ThreadedSEState:
        if m is None:
            m = self.get_memory_model().create_memory()
        # if self.get_options().incremental_solving:
        #    return IncrementalSEState(self, pc, m)
        return ThreadedSEState(self, pc, m, self.solver)

    def exec_undef_fun(self, state, instr, fun):
        fnname = fun.name()
        if fnname == "__VERIFIER_atomic_begin":
            state.start_atomic()
            state.pc = state.pc.get_next_inst()
            return [state]
        if fnname == "__VERIFIER_atomic_end":
            state.end_atomic()
            state.pc = state.pc.get_next_inst()
            return [state]
        if fnname == "pthread_mutex_init":
            state.mutex_init(state.eval(instr.operand(0)))
            # return non-det value for the init
            # TODO: we should connect the returned value with the
            # effect of init...
            return super().exec_undef_fun(state, instr, fun)
        if fnname == "pthread_mutex_destroy":
            state.mutex_destroy(state.eval(instr.operand(0)))
            # the same as for init...
            return super().exec_undef_fun(state, instr, fun)
        if fnname == "pthread_mutex_lock":
            mtx = state.eval(instr.operand(0))
            # TODO: This does not work with mutexes initialized via assignment...
            # if not state.has_mutex(mtx):
            #    state.set_killed("Locking unknown mutex")
            #    return [state]
            lckd = state.mutex_locked_by(mtx)
            if lckd is not None:
                if lckd == state.thread().get_id():
                    state.set_killed("Double lock")
                else:
                    state.mutex_wait(mtx)
            else:
                state.mutex_lock(mtx)
                state.pc = state.pc.get_next_inst()
            return [state]
        if fnname == "pthread_mutex_unlock":
            mtx = state.eval(instr.operand(0))
            if not state.has_mutex(mtx):
                state.set_killed("Unlocking unknown mutex")
                return [state]
            lckd = state.mutex_locked_by(mtx)
            if lckd is None:
                state.set_killed("Unlocking unlocked lock")
            else:
                if lckd != state.thread().get_id():
                    state.set_killed("Unlocking un-owned mutex")
                else:
                    state.mutex_unlock(mtx)
                    state.pc = state.pc.get_next_inst()
            return [state]
        if fnname.startswith("pthread_"):
            state.set_killed(f"Unsupported pthread_* API: {fnname}")
            return [state]
        return super().exec_undef_fun(state, instr, fun)

    def call_fun(self, state, instr, fun):
        if fun.name().startswith("__VERIFIER_atomic_"):
            state.start_atomic()
        return super().call_fun(state, instr, fun)

    def exec_thread(self, state, instr):
        fun = instr.called_function()
        ldbgv("-- THREAD {0} --", (fun.name(),))
        if fun.is_undefined():
            state.set_error(
                GenericError(f"Spawning thread with undefined function: {fun.name()}")
            )
            return [state]
        # map values to arguments
        # TODO: do we want to allow this? Less actual parameters than formal parameters?
        # assert len(instr.operands()) == len(fun.arguments())
        if len(instr.operands()) > len(fun.arguments()):
            dbgv(
                "Thread created with less actual arguments than with formal arguments..."
            )
        assert len(instr.operands()) >= len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        t = state.add_thread(fun, fun.bblock(0).instruction(0), mapping or {})

        # we executed the thread inst, so move
        state.pc = state.pc.get_next_inst()
        state.set(instr, concrete_value(t.get_id(), get_offset_type()))
        return [state]

    # def exec_thread_exit(self, state, instr: ThreadExit):
    #    assert isinstance(instr, ThreadExit)

    #    # obtain the return value (if any)
    #    ret = None
    #    if len(instr.operands()) != 0:  # returns something
    #        ret = state.eval(instr.operand(0))
    #        assert (
    #            ret is not None
    #        ), f"No return value even though there should be: {instr}"

    #    state.exit_thread(ret)
    #    return [state]

    def exec_thread_join(self, state, instr: ThreadJoin):
        assert isinstance(instr, ThreadJoin)
        assert len(instr.operands()) == 1
        tid = state.eval(instr.operand(0))
        if not tid.is_concrete():
            state.set_killed("Symbolic thread values are unsupported yet")
        else:
            state.join_threads(tid.value())
        return [state]

    def exec_ret(self, state, instr: Return):
        assert isinstance(instr, Return)

        # obtain the return value (if any)
        ret = None
        if len(instr.operands()) != 0:  # returns something
            ret = state.eval(instr.operand(0))
            assert (
                ret is not None
            ), f"No return value even though there should be: {instr}"

        if state.frame().function.name().startswith("__VERIFIER_atomic_"):
            state.end_atomic()
        # pop the call frame and get the return site
        rs = state.pop_call()
        if rs is None:  # popped the last frame
            # if ret is not None and ret.is_pointer():
            #    state.set_error(GenericError("Returning a pointer from main function"))
            #    return [state]

            # if state.thread().get_id() == 0:
            #    # this is the main thread exiting, exit the whole program
            #    # FIXME: we should call dtors and so on...
            #    state.set_exited(0)
            # else:
            #    # this is the same as calling pthread_exit
            #    # FIXME: set the retval to 'ret'
            #    state.exit_thread()
            state.exit_thread(ret)
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.get_next_inst()
        return [state]

    def execute(self, state, instr):
        # state._trace.append(
        #    "({2}) {0}: {1}".format(
        #        "--" if not instr.bblock() else instr.fun().name(),
        #        instr,
        #        state.thread().get_id(),
        #    ),
        # )

        if isinstance(instr, Thread):
            return self.exec_thread(state, instr)
        if isinstance(instr, ThreadJoin):
            return self.exec_thread_join(state, instr)
        return super().execute(state, instr)
