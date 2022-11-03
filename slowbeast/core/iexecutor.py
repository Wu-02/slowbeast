import sys
from typing import List, Optional

from slowbeast.core.executionstate import ExecutionState
from slowbeast.domains.pointer import Pointer
from slowbeast.ir.instruction import *
from slowbeast.ir.program import Program
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.memorymodel import SymbolicMemoryModel
from slowbeast.symexe.options import SEOptions
from slowbeast.util.debugging import ldbgv
from .errors import GenericError
from .memorymodel import MemoryModel
from ..domains.concrete_bitvec import ConcreteBitVec


class IExecutor:
    """
    Class that takes care of executing single instructions.
    That is, the executor takes a state, executes one instruction
    and generates new states.

    It is called IExecutor to highlight that it executes only instructions,
    not whole programs.
    """

    def __init__(
        self,
        program: Program,
        opts: SEOptions,
        memorymodel: Optional[SymbolicMemoryModel] = None,
    ) -> None:
        self.memorymodel = memorymodel or MemoryModel(opts)

        self._program = program
        self._opts = opts
        self._executed_instrs = 0
        self._executed_blks = 0

    # def set_memory_model(self, mm):
    #    self.memorymodel = mm

    def get_memory_model(self) -> SymbolicMemoryModel:
        assert self.memorymodel is not None
        return self.memorymodel

    def create_state(self, pc=None, m=None) -> ExecutionState:
        """
        Create a state that can be processed by this executor.
        """
        if m is None:
            m = self.memorymodel.create_memory()
        return ExecutionState(pc, m)

    def get_exec_instr_num(self) -> int:
        return self._executed_instrs

    def get_exec_step_num(self) -> int:
        return self._executed_blks

    def get_options(self) -> SEOptions:
        return self._opts

    def forbid_calls(self) -> None:
        self._opts.no_calls = True

    def calls_forbidden(self) -> bool:
        return self._opts.no_calls

    def exec_store(self, state: SEState, instr: Store) -> List[SEState]:
        assert isinstance(instr, Store)

        states = self.memorymodel.write(
            state, instr, instr.value_operand(), instr.pointer_operand()
        )

        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def exec_load(self, state: SEState, instr: Load) -> List[SEState]:
        assert isinstance(instr, Load)

        states = self.memorymodel.read(
            state, instr, instr.pointer_operand(), instr.bytewidth(), instr.bitwidth()
        )

        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def exec_alloc(self, state: SEState, instr: Alloc) -> List[SEState]:
        states = self.memorymodel.allocate(state, instr)
        for s in states:
            if s.is_ready():
                s.pc = s.pc.get_next_inst()
        return states

    def exec_cmp(self, state, instr: Cmp):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.operand(0))
        op2 = state.eval(instr.operand(1))
        if op1.is_pointer():
            if not op2.is_pointer():
                raise RuntimeError("Comparison of pointer to a constant")
            if op1.object.get_id() != op2.object.get_id():
                raise RuntimeError("Comparison of unrelated pointers")
            op1 = op1.offset
            op2 = op2.offset
        else:
            op1 = op1.value()
            op2 = op2.value()
        x = None
        p = instr.predicate()
        if p == Cmp.LE:
            x = op1 <= op2
        elif p == Cmp.LT:
            x = op1 < op2
        elif p == Cmp.GE:
            x = op1 >= op2
        elif p == Cmp.GT:
            x = op1 > op2
        elif p == Cmp.EQ:
            x = op1 == op2
        elif p == Cmp.NE:
            x = op1 != op2

        state.set(instr, ConcreteBitVec(x, 1))
        state.pc = state.pc.get_next_inst()

        return [state]

    def exec_print(self, state: SEState, instr: Print) -> List[SEState]:
        assert isinstance(instr, Print)
        for x in instr.operands():
            v = state.eval(x)
            if v.is_concrete():
                v = v.value()
            sys.stdout.write(str(v))
        sys.stdout.write("\n")
        sys.stdout.flush()

        state.pc = state.pc.get_next_inst()

        return [state]

    def exec_branch(self, state, instr: Branch):
        assert isinstance(instr, Branch)
        c = instr.condition()
        assert isinstance(c, ValueInstruction) or c.is_concrete()
        cv = state.eval(instr.condition()).value()

        if cv:
            succ = instr.true_successor()
        elif cv == False:
            succ = instr.false_successor()
        else:
            raise RuntimeError("Indeterminite condition")

        assert succ
        if not succ.empty():
            state.pc = succ.instruction(0)
        else:
            state.pc = None

        return [state]

    def exec_switch(self, state, instr: Switch):
        assert isinstance(instr, Switch)
        # c = instr.condition()
        # assert isinstance(c, ValueInstruction) or c.is_concrete()
        # cv = state.eval(instr.condition()).value()
        raise RuntimeError("Not implemented")

    def exec_assert(self, state, instr: Assert):
        assert isinstance(instr, Assert)
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_concrete()
            if v.value() != True:
                state.set_error(
                    AssertFailError(f"Assertion failed: {o} is {v} (!= True)")
                )
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assume(self, state, instr: Assume):
        assert isinstance(instr, Assume)
        state.pc = state.pc.get_next_inst()
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_concrete()
            assert v.is_bool()
            if v.value() != True:
                print(f"Assumption failed: {o} == {v} (!= True)")
                state.dump()
                break

        return [state]

    def exec_unary_op(self, state, instr):
        raise NotImplementedError("Concrete executor does not implement unary op yet")

    def exec_binary_op(self, state, instr: BinaryOperation):
        assert isinstance(instr, BinaryOperation)
        op1c = state.eval(instr.operand(0))
        op2c = state.eval(instr.operand(1))
        op1 = None
        op2 = None
        bw = max(op1c.bytewidth(), op2c.bytewidth())
        # if one of the operands is a pointer,
        # lift the other to pointer too
        if op1c.is_pointer():
            if not op2c.is_pointer():
                assert op2c.is_concrete()
                # adding a constant -- create a pointer
                # to the object with the right offset
                op2c = Pointer(op1c.object, op2c.value())
        elif op2c.is_pointer():
            if not op1c.is_pointer():
                assert op1c.is_concrete()
                # adding a constant -- create a pointer
                # to the object with the right offset
                op1c = Pointer(op2c.object, op1c.value())
        else:
            op1 = op1c.value()
            op2 = op2c.value()

        if op1c.is_pointer() and op1c.object != op2c.object:
            raise RuntimeError("Pointer arithmetic on unrelated pointers")

        r = None
        if instr.operation() == BinaryOperation.ADD:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset + op2c.offset)
            else:
                r = ConcreteBitVec(op1 + op2, bw)
        elif instr.operation() == BinaryOperation.SUB:
            if isinstance(op1c, Pointer):
                assert isinstance(op2c, Pointer)
                r = Pointer(op1c.object, op1c.offset - op2c.offset)
            else:
                r = ConcreteBitVec(op1 - op2, bw)
        elif instr.operation() == BinaryOperation.MUL:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset * op2c.offset)
            else:
                r = ConcreteBitVec(op1 * op2, bw)
        elif instr.operation() == BinaryOperation.DIV:
            if op1c.is_pointer():
                assert op2c.is_pointer()
                r = Pointer(op1c.object, op1c.offset / op2c.offset)
            else:
                r = ConcreteBitVec(op1 / op2, bw)
        else:
            raise NotImplementedError("Binary operation: " + str(instr))

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_ite(self, state, instr):
        raise NotImplementedError("Ite not implemented in core")

    def exec_call(self, state, instr: Call):
        assert isinstance(instr, Call)

        if self.calls_forbidden():
            state.set_killed("Calls are forbidden")
            return [state]

        fun = instr.called_function()
        ldbgv("-- CALL {0} --", (fun.name()))
        if fun.is_undefined():
            state.set_error(GenericError(f"Called undefined function: {fun.name()}"))
            return [state]
        # map values to arguments
        assert len(instr.operands()) == len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        state.push_call(instr, fun, mapping)
        return [state]

    def exec_ret(self, state: SEState, instr: Return) -> List[SEState]:
        assert isinstance(instr, Return)

        # obtain the return value (if any)
        ret = None
        if len(instr.operands()) != 0:  # returns something
            ret = state.eval(instr.operand(0))
            assert (
                ret is not None
            ), f"No return value even though there should be: {instr}"

        # pop the call frame and get the return site
        rs = state.pop_call()
        if rs is None:  # popped the last frame
            if ret is not None and ret.is_pointer():
                state.set_error(GenericError("Returning a pointer from main function"))
                return [state]
            # elif not ret.is_concrete():
            #    state.add_warning(
            #        "Returning a non-constant value from the main function"
            #    )

            state.set_exited(ret)
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.get_next_inst()
        return [state]

    def execute(
        self,
        state: SEState,
        instr: Union[
            Alloc,
            Assert,
            Assume,
            BinaryOperation,
            Branch,
            Call,
            Cmp,
            Ite,
            Load,
            Print,
            Return,
            Store,
            Switch,
            Thread,
            ThreadExit,
            ThreadJoin,
            UnaryOperation,
        ],
    ) -> List[SEState]:
        """
        Execute the next instruction in the state and modify the state accordingly.
        """
        # debug print
        ldbgv(
            "({2}) {0}: {1}",
            (
                "--" if not instr.bblock() else instr.fun().name(),
                instr,
                state.get_id(),
            ),
            verbose_lvl=3,
        )

        self._executed_instrs += 1

        # TODO: add an opcode to instruction and check only the opcode
        states = None
        if isinstance(instr, Store):
            states = self.exec_store(state, instr)
        elif isinstance(instr, Load):
            states = self.exec_load(state, instr)
        elif isinstance(instr, Alloc):
            states = self.exec_alloc(state, instr)
        elif isinstance(instr, Cmp):
            states = self.exec_cmp(state, instr)
        elif isinstance(instr, Print):
            states = self.exec_print(state, instr)
        elif isinstance(instr, Branch):
            states = self.exec_branch(state, instr)
        elif isinstance(instr, Assert):
            states = self.exec_assert(state, instr)
        elif isinstance(instr, Assume):
            states = self.exec_assume(state, instr)
        elif isinstance(instr, UnaryOperation):
            states = self.exec_unary_op(state, instr)
        elif isinstance(instr, BinaryOperation):
            states = self.exec_binary_op(state, instr)
        elif isinstance(instr, Ite):
            states = self.exec_ite(state, instr)
        elif isinstance(instr, (Thread, ThreadExit, ThreadJoin)):
            # XXX: must be before Call and Return
            state.set_killed(f"Threads are not implemented by this executor: {instr}")
            return [state]
        elif isinstance(instr, Call):
            states = self.exec_call(state, instr)
        elif isinstance(instr, Return):
            states = self.exec_ret(state, instr)
        elif isinstance(instr, Switch):
            states = self.exec_switch(state, instr)
        else:
            state.set_killed(f"Not implemented instruction: {instr}")
            return [state]

        return states

    def execute_seq(self, state, instrs):
        """
        Execute instructions 'instrs' from state(s) 'state'. The instructions
        must not contain Branch instruction. \return two list, the first
        contains READY states and the other contains not READY states.
        """
        nonreadystates = []
        if isinstance(state, list):
            readystates = state
        else:
            readystates = [state]

        execute = self.execute
        nonreadystatesappend = nonreadystates.append
        for i in instrs:
            assert not isinstance(i, Branch), "Branch instruction in execute_seq"

            newst = []
            newstappend = newst.append
            for s in readystates:
                s.pc = i
                nxt = execute(s, i)
                for n in nxt:
                    if n.is_ready():
                        newstappend(n)
                    else:
                        nonreadystatesappend(n)

            readystates = newst
            if not readystates:
                break

        return readystates, nonreadystates

    def execute_till_branch(
        self, state: SEState, stopBefore: bool = False
    ) -> List[SEState]:
        """
        Start executing from 'state' and stop execution after executing a
        branch instruction.  This will typically execute exactly one basic block
        of the code.
        If 'stopBefore' is True, stop the execution before executing the
        branch instruction.
        """
        self._executed_blks += 1

        finalstates = []
        if isinstance(state, list):
            readystates = state
        else:
            readystates = [state]

        execute = self.execute
        finalstatesappend = finalstates.append
        while readystates:
            newst = []
            newstappend = newst.append
            for s in readystates:
                pc = s.pc
                # remember that it is a branch now,
                # because execute() will change pc
                isbranch = isinstance(pc, Branch)
                if stopBefore and isbranch:
                    finalstatesappend(s)
                    continue

                nxt = execute(s, pc)
                if isbranch:
                    # we stop here
                    finalstates += nxt
                else:
                    for n in nxt:
                        if n.is_ready():
                            newstappend(n)
                        else:
                            finalstatesappend(n)

            readystates = newst

        assert not readystates
        return finalstates

    def execute_path(self, state, path):
        """
        Execute the given path through CFG. Return two lists of states.
        The first list contains the resulting states that reaches the
        end of the path, the other list contains all other states, i.e.,
        the error, killed or exited states reached during the execution of the CFG.
        """

        if isinstance(state, list):
            states = state
        else:
            states = [state]

        earlytermstates = []
        idx = 0

        locs = path.locations()
        # set the pc of the states to be the first instruction of the path
        for s in states:
            assert s.is_ready()
            s.pc = locs[0].bblock().first()

        for idx in range(0, len(locs)):
            # execute the block till branch
            newstates = self.execute_till_branch(states, stopBefore=True)

            # get the ready states
            states = []
            for n in newstates:
                (states, earlytermstates)[0 if n.is_ready() else 1].append(n)

            # now execute the branch following the edge on the path
            if idx + 1 < len(locs):
                curbb = locs[idx].bblock()
                succbb = locs[idx + 1].bblock()
                followsucc = curbb.last().true_successor() == succbb
                newstates = []
                assert followsucc or curbb.last().false_successor() == succbb
                for s in states:
                    assert s.is_ready()
                    newstates += self.exec_branch_to(s, s.pc, followsucc)
            else:  # this is the last location on path,
                # so just normally execute the block instructions
                newstates = self.execute_till_branch(states)
            states = newstates

        assert all(map(lambda x: not x.is_ready(), earlytermstates))

        return states, earlytermstates
