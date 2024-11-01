from slowbeast.domains.concrete import ConcreteDomain
from ..domains.concrete_bitvec import ConcreteBitVec
from ..domains.concrete_value import ConcreteBool
from slowbeast.domains.pointer import Pointer

# from slowbeast.domains.sign import ZODomain
from slowbeast.domains.signul import SignULDomain, SignULDomain as Domain
from slowbeast.domains.value import Value
from .executionstate import AbstractState
from .memory import AIMemoryModel
from ..core.errors import AssertFailError
from ..core.iexecutor import IExecutor as ConcreteExecutor
from ..ir.instruction import *
from ..util.debugging import dbgv
from slowbeast.ai.executionstate import AbstractState
from slowbeast.ai.memory import AIMemoryModel
from slowbeast.ir.instruction import (
    Assert,
    Assume,
    BinaryOperation,
    Branch,
    Call,
    Cmp,
    UnaryOperation,
    ValueInstruction,
)
from typing import Optional


class AIStats:
    def __init__(self) -> None:
        # number of branch instructions
        self.branchings = 0
        # number of branch instructions where we forked
        self.branch_forks = 0
        # number of times we called fork()
        self.fork_calls = 0
        # number of times when the call to fork() forked the execution
        self.forks = 0


def add_pointer_with_constant(E, op1, op2) -> Pointer:
    return Pointer(op1.object(), Domain.Add(op1.offset(), op2))


def eval_condition(state, cond: ValueInstruction) -> Value:
    assert isinstance(cond, ValueInstruction) or cond.is_concrete()
    c = state.eval(cond)
    assert isinstance(c, Value)
    # solvers make difference between bitvectors and booleans, so we must
    # take care of it here: if it is a bitvector, compare it to 0 (C
    # semantics)
    ty = c.type()
    if not ty.is_bool():
        assert ty.bitwidth() == 1, f"Invalid condition in branching: {c} {(type(c))}"
        cval = Domain.Ne(c, Domain.lift(ConcreteBitVec(0, 1)))
    else:
        cval = c  # It already is a boolean expression

    return cval


class IExecutor(ConcreteExecutor):
    def __init__(
        self, program, opts, memorymodel: Optional[AIMemoryModel] = None
    ) -> None:
        if memorymodel is None:
            memorymodel = AIMemoryModel(opts)
        super(IExecutor, self).__init__(program, opts, memorymodel)
        self.stats = AIStats()

    def is_error_fn(self, fun: str):
        if isinstance(fun, str):
            return fun in self.get_options().error_funs
        return fun.name() in self.get_options().error_funs

    def error_funs(self):
        return self.get_options()._error_funs

    def create_state(self, pc=None, m=None) -> AbstractState:
        if m is None:
            m = self.get_memory_model().create_memory()
        return AbstractState(self, pc, m)

    def create_clean_state(self, pc=None, m=None) -> AbstractState:
        s = self.create_state(pc, m)
        s.push_call(None)
        return s

    def fork(self, state, condinst, cond: SignULDomain):
        self.stats.fork_calls += 1

        T, F = None, None

        # fast path + do not add True/False to constraints
        if cond.is_concrete():
            assert cond.is_bool(), "Invalid constant"
            if cond.value():
                return state, None
            elif not cond.value():
                return None, state
            else:
                raise RuntimeError(f"Invalid condition: {cond.value()}")

        # check SAT of cond and its negation
        csat = state.is_sat(cond)
        if csat is None:
            T = state.copy()
            T.set_killed(f"Solver failure: {r}")

        ncond = Domain.Not(cond)
        ncsat = state.is_sat(ncond)
        if ncsat is None:
            F = state.copy()
            F.set_killed(f"Solver failure: {r}")

        # is one of the conditions implied?
        # in that case we do not need to add any constraint
        if csat is True and ncsat is False:
            return state, None
        elif ncsat is True and csat is False:
            return None, state
        else:
            if csat is True:
                T = state.copy()
                T.set(condinst, Domain.lift(ConcreteBool(True)))

            if ncsat is True:
                F = state.copy()
                F.set(condinst, Domain.lift(ConcreteBool(False)))

            if T and F:
                self.stats.forks += 1

        return T, F

    def assume(self, state, condinst, cond) -> None:
        """Put an assumption _into_ the given state.
        Return the state or None if that situation cannot happen
        (the assumption is inconsistent with the state).
        """
        if cond.is_concrete():
            assert cond.is_bool(), "Invalid constant"
            if cond.value():
                return state
            else:
                return None

        r = state.is_sat(cond)
        if r is None:
            return None
        elif r:
            state.set(condinst, cond)
            return state
        return None

    def exec_branch_to(self, state, instr: Branch, to: bool):
        """
        Execute a branch instruction and follow the given successor
        (True or False successor).
        """
        assert isinstance(instr, Branch)
        assert isinstance(to, bool)
        dbgv(f"branching to {to} succ of {instr}")
        self.stats.branchings += 1

        cond = instr.condition()
        cval = eval_condition(state, cond)

        succ = None
        if to is True:
            s = self.assume(state, cond, cval)
            succ = instr.true_successor()
        elif to is False:
            s = self.assume(state, cond, Domain.Not(cval))
            succ = instr.false_successor()
        else:
            raise RuntimeError(f"Invalid branch successor: {to}")

        if s is None:
            dbgv("branching is not feasible!")
            return []
        else:
            assert succ
            s.pc = succ.instruction(0)

        return [s]

    def exec_branch(self, state, instr: Branch):
        assert isinstance(instr, Branch)
        self.stats.branchings += 1

        cond = instr.condition()
        cval = eval_condition(state, cond)

        true_branch, false_branch = self.fork(state, cond, cval)
        # at least one must be feasable...
        assert true_branch or false_branch, "Fatal Error: failed forking condition"

        states = []
        if true_branch:
            true_branch.pc = instr.true_successor().instruction(0)
            states.append(true_branch)
        if false_branch:
            false_branch.pc = instr.false_successor().instruction(0)
            states.append(false_branch)

        if true_branch and false_branch:
            self.stats.branch_forks += 1

        return states

    def compare_values(self, E, p, op1, op2, unsgn):
        if p == Cmp.LE:
            return E.Le(op1, op2, unsgn)
        elif p == Cmp.LT:
            return E.Lt(op1, op2, unsgn)
        elif p == Cmp.GE:
            return E.Ge(op1, op2, unsgn)
        elif p == Cmp.GT:
            return E.Gt(op1, op2, unsgn)
        elif p == Cmp.EQ:
            return E.Eq(op1, op2, unsgn)
        elif p == Cmp.NE:
            return E.Ne(op1, op2, unsgn)
        else:
            raise RuntimeError("Invalid comparison")

    def compare_pointers(self, state, instr, p1, p2):
        mo1 = p1.object()
        mo2 = p2.object()
        if not ConcreteDomain.belongto(mo1, mo2):
            state.set_killed(f"Comparison of symbolic pointers unimplemented: {instr}")
            return [state]

        p = instr.predicate()
        if mo1.get_id() == mo2.get_id():
            state.set(
                instr,
                self.compare_values(
                    Domain, p, p1.offset(), p2.offset(), instr.is_unsigned()
                ),
            )
            state.pc = state.pc.get_next_inst()
            return [state]
        else:
            if p != Cmp.EQ and p != Cmp.NE:
                state.set_killed(
                    "Comparison of pointers implemented only for "
                    "(non-)equality or into the same object"
                )
                return [state]
            else:
                state.set(instr, ConcreteBool(p == Cmp.NE))
                state.pc = state.pc.get_next_inst()
                return [state]

        raise RuntimeError("Invalid pointer comparison")

    def exec_cmp(self, state, instr: Cmp):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.operand(0))
        op2 = state.eval(instr.operand(1))

        if op1.is_pointer() or op2.is_pointer():
            if op1.is_pointer() and op2.is_pointer():
                return self.compare_pointers(state, instr, op1, op2)
            else:
                state.set_killed("Comparison of pointer to a constant not implemented")
                return state

        x = self.compare_values(
            Domain, instr.predicate(), op1, op2, instr.is_unsigned()
        )
        state.set(instr, x)
        state.pc = state.pc.get_next_inst()

        return [state]

    def exec_call(self, state, instr: Call):
        assert isinstance(instr, Call)
        fun = instr.called_function()
        if self.is_error_fn(fun):
            state.set_error(AssertFailError(f"Called '{fun.name()}'"))
            return [state]

        if fun.is_undefined():
            return self.exec_undef_fun(state, instr, fun)

        if self.calls_forbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.set_killed(f"calling '{fun.name()}', but calls are forbidden")
            return [state]

        # map values to arguments
        assert len(instr.operands()) == len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        state.push_call(instr, fun, mapping)
        return [state]

    def exec_undef_fun(self, state, instr, fun):
        name = fun.name()
        if name == "abort":
            state.set_terminated("Aborted via an abort() call")
            return [state]

        ret_ty = fun.return_type()
        if ret_ty:
            val = Domain.symbolic_value(ret_ty)
            # state.addNondet(val)
            state.set(instr, val)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_binary_op(self, state, instr: BinaryOperation):
        assert isinstance(instr, BinaryOperation)
        op1 = state.eval(instr.operand(0))
        op2 = state.eval(instr.operand(1))
        # if one of the operands is a pointer,
        # lift the other to pointer too
        r = None
        if op1.is_pointer():
            if not op2.is_pointer():
                r = add_pointer_with_constant(Domain, op1, op2)
            else:
                state.set_killed(f"Arithmetic on pointers not implemented yet: {instr}")
                return [state]
        elif op2.is_pointer():
            if not op1.is_pointer():
                r = add_pointer_with_constant(Domain, op2, op1)
            else:
                state.set_killed(f"Arithmetic on pointers not implemented yet: {instr}")
                return [state]
        else:
            if instr.operation() == BinaryOperation.ADD:
                r = Domain.Add(op1, op2)
            elif instr.operation() == BinaryOperation.SUB:
                r = Domain.Sub(op1, op2)
            elif instr.operation() == BinaryOperation.MUL:
                r = Domain.Mul(op1, op2)
            elif instr.operation() == BinaryOperation.DIV:
                r = Domain.Div(op1, op2, instr.is_unsigned())
            elif instr.operation() == BinaryOperation.SHL:
                r = Domain.Shl(op1, op2)
            elif instr.operation() == BinaryOperation.LSHR:
                r = Domain.LShr(op1, op2)
            elif instr.operation() == BinaryOperation.ASHR:
                r = Domain.AShr(op1, op2)
            elif instr.operation() == BinaryOperation.REM:
                r = Domain.Rem(op1, op2, instr.is_unsigned())
            elif instr.operation() == BinaryOperation.AND:
                r = Domain.And(op1, op2)
            elif instr.operation() == BinaryOperation.OR:
                r = Domain.Or(op1, op2)
            elif instr.operation() == BinaryOperation.XOR:
                r = Domain.Xor(op1, op2)
            else:
                state.set_killed(f"Not implemented binary operation: {instr}")
                return [state]

        assert r, "Bug in creating a binary op expression"

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_unary_op(self, state, instr: UnaryOperation):
        assert isinstance(instr, UnaryOperation)
        op1 = state.eval(instr.operand(0))
        if instr.operation() == UnaryOperation.ZEXT:
            bw = instr.bitwidth()
            r = Domain.ZExt(op1, bw)
        elif instr.operation() == UnaryOperation.SEXT:
            bw = instr.bitwidth()
            r = Domain.SExt(op1, bw)
        elif instr.operation() == UnaryOperation.CAST:
            r = Domain.Cast(op1, instr.casttype())
            if r is None:
                state.set_killed(f"Unsupported/invalid cast: {instr}")
                return [state]
        elif instr.operation() == UnaryOperation.EXTRACT:
            start, end = instr.range()
            r = Domain.Extract(op1, start, end)
        elif instr.operation() == UnaryOperation.NEG:
            r = Domain.Neg(op1)
        else:
            state.set_killed(f"Unary instruction not implemented: {instr}")
            return [state]

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assume(self, state, instr: Assume):
        assert isinstance(instr, Assume)
        for o in instr.operands():
            v = state.eval(o)
            assert v.is_bool()
            if v.is_concrete():
                assert isinstance(v.value(), bool)
                isunsat = not v.value()
            else:
                tmp = self.assume(state, o, v)
                isunsat = tmp is None

            if isunsat:
                state.set_terminated(f"Assumption unsat: {o} == {v} (!= True)")
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assert(self, state, instr: Assert):
        assert isinstance(instr, Assert)
        o = instr.condition()
        msg = instr.msg()
        if not msg:
            msg = str(o)
        v = state.eval(o)
        states = []
        assert v.is_bool(), f"Evaluated condition is not boolean: {v}"
        if v.is_concrete():
            if v.value() is not True:
                state.set_error(AssertFailError(msg))
            else:
                state.pc = state.pc.get_next_inst()
            states.append(state)
        else:
            ok_branch, err_branch = self.fork(state, o, v)
            if ok_branch:
                ok_branch.pc = ok_branch.pc.get_next_inst()
                states.append(ok_branch)
            if err_branch:
                err_branch.set_error(AssertFailError(msg))
                states.append(err_branch)

        assert states, "Generated no states"
        return states

    def concretize(self, state, val):
        if val.is_concrete():
            return val

        return state.solver().concretize(val, *state.constraints())
