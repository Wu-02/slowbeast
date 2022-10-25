from random import getrandbits

import slowbeast.domains.concrete_value
from slowbeast.core.errors import AssertFailError
from slowbeast.core.executor import Executor as ConcreteExecutor
from slowbeast.domains import dom_is_concrete
from ..domains.concrete_value import ConcreteVal, ConcreteBool
from slowbeast.domains.pointer import Pointer
from slowbeast.domains.value import Value
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import *
from slowbeast.util.debugging import dbgv, ldbgv, warn
from .executionstate import IncrementalSEState
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.memorymodel import SymbolicMemoryModel
from slowbeast.symexe.statesset import StatesSet
from typing import Optional

unsupported_funs = [
    "memmove",
    "memcpy",
    "llvm.memmove.p0i8.p0i8.i32",
    "llvm.memmove.p0i8.p0i8.i64",
    "llvm.memcpy.p0i8.p0i8.i32",
    "llvm.memcpy.p0i8.p0i8.i64",
]


def _types_check(instr: Instruction, *vals):
    if __debug__:
        for expected, real in zip(instr.expected_op_types(), vals):
            if expected == real:
                warn(f"Expected type '{expected}' is different from real '{real}'")
                return False
    return True


class SEStats:
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
    return Pointer(op1.object(), E.Add(op1.offset(), op2))


def condition_to_bool(cond, EM):
    if cond.type().is_bool():
        return cond

    if cond.is_concrete():
        cval = EM.Ne(cond, ConcreteVal(0, cond.type()))
    else:
        assert cond.is_symbolic()
        assert not cond.type().is_bool()
        assert cond.type().bitwidth() == 1, f"Invalid condition in branching: {cond}"
        cval = EM.Ne(cond, ConcreteVal(0, cond.type()))

    assert cval.is_bool()
    return cval


def eval_condition(state, cond: ValueInstruction):
    assert isinstance(cond, ValueInstruction) or cond.is_concrete()
    c = state.eval(cond)
    assert isinstance(c, Value)
    # solvers make difference between bitvectors and booleans, so we must
    # take care of it here: if it is a bitvector, compare it to 0 (C
    # semantics)
    return condition_to_bool(c, state.expr_manager())


class Executor(ConcreteExecutor):
    def __init__(
        self, program, solver, opts, memorymodel: Optional[SymbolicMemoryModel] = None
    ) -> None:
        if memorymodel is None:
            memorymodel = SymbolicMemoryModel(opts)
        super().__init__(program, opts, memorymodel)
        self.solver = solver
        self.stats = SEStats()
        # use these values in place of nondet values
        self._input_vector = None

    def is_error_fn(self, fun: str):
        if isinstance(fun, str):
            return fun in self.get_options().error_funs
        return fun.name() in self.get_options().error_funs

    def error_funs(self):
        return self._error_funs

    def set_input_vector(self, ivec) -> None:
        self._input_vector = ivec.copy()
        # reverse the vector so that we can pop from it
        self._input_vector.reverse()

    def create_state(self, pc=None, m=None) -> SEState:
        if m is None:
            m = self.get_memory_model().create_memory()
        if self.get_options().incremental_solving:
            s = IncrementalSEState(self, pc, m)
        else:
            # FIXME: we do not use the solver...
            s = SEState(self, pc, m, self.solver)
        assert not s.constraints(), "the state is not clean"
        return s

    def create_clean_state(self, pc=None, m=None) -> SEState:
        s = self.create_state(pc, m)
        s.push_call(None)
        return s

    def create_states_set(self, S=None) -> StatesSet:
        ss = StatesSet(self.create_clean_state())
        if S:
            # set the set to be S
            ss.intersect(S)
        return ss

    def fork(self, state, cond):
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
            T.set_killed(f"Solver failure: {csat}")

        ncond = state.expr_manager().Not(cond)
        ncsat = state.is_sat(ncond)
        if ncsat is None:
            F = state.copy()
            F.set_killed(f"Solver failure: {ncsat}")

        # is one of the conditions implied?
        # in that case we do not need to add any constraint
        if csat is True and ncsat is False:
            return state, None
        elif ncsat is True and csat is False:
            return None, state
        else:
            if csat is True:
                T = state.copy()
                T.add_constraint(cond)

            if ncsat is True:
                F = state.copy()
                F.add_constraint(ncond)

            if T and F:
                self.stats.forks += 1

        return T, F

    # FIXME: make this a method of State?
    def assume(self, state, cond) -> None:
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
            state.add_constraint(cond)
            return state
        return None

    def exec_branch_to(self, state, instr: Branch, to: bool):
        """
        Execute a branch instruction and follow the given successor
        (True or False successor).
        """
        assert isinstance(instr, Branch)
        assert isinstance(to, bool)
        ldbgv("branching to {0} succ of {1}", (to, instr))
        self.stats.branchings += 1

        cond = instr.condition()
        cval = eval_condition(state, cond)

        succ = None
        if to is True:
            s = self.assume(state, cval)
            succ = instr.true_successor()
        elif to is False:
            s = self.assume(state, state.expr_manager().Not(cval))
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
        assert cond.type().is_bool()
        cval = eval_condition(state, cond)
        assert cval.type().is_bool()

        trueBranch, falseBranch = self.fork(state, cval)
        # at least one must be feasable...
        assert trueBranch or falseBranch, "Fatal Error: failed forking condition"

        states = []
        if trueBranch:
            trueBranch.pc = instr.true_successor().instruction(0)
            states.append(trueBranch)
        if falseBranch:
            falseBranch.pc = instr.false_successor().instruction(0)
            states.append(falseBranch)

        if trueBranch and falseBranch:
            self.stats.branch_forks += 1

        return states

    def exec_switch(self, state, instr: Switch):
        assert isinstance(instr, Switch)
        self.stats.branchings += 1

        cond = state.eval(instr.condition())
        assert instr.condition().type().is_bv()
        assert cond.type().is_bv()
        Eq = state.expr_manager().Eq
        fork = self.fork
        states = []
        for v, bb in instr.cases():
            true_branch, state = fork(state, Eq(cond, v))
            if true_branch:
                true_branch.pc = bb.instruction(0)
                states.append(true_branch)
            if state is None:
                break

        # the default branch
        if state:
            state.pc = instr.default_bblock().instruction(0)
            states.append(state)

        self.stats.branch_forks += len(states) - 1
        return states

    def compare_values(self, expr_mgr, p, op1, op2, unsgn):
        if p == Cmp.LE:
            return expr_mgr.Le(op1, op2, unsgn)
        elif p == Cmp.LT:
            return expr_mgr.Lt(op1, op2, unsgn)
        elif p == Cmp.GE:
            return expr_mgr.Ge(op1, op2, unsgn)
        elif p == Cmp.GT:
            return expr_mgr.Gt(op1, op2, unsgn)
        elif p == Cmp.EQ:
            return expr_mgr.Eq(op1, op2, unsgn)
        elif p == Cmp.NE:
            return expr_mgr.Ne(op1, op2, unsgn)
        else:
            raise RuntimeError("Invalid comparison")

    def compare_pointers(self, state, instr, p1, p2):
        mo1id = p1.object()
        mo2id = p2.object()
        if mo1id.is_symbolic() or mo2id.is_symbolic():
            state.set_killed(f"Comparison of symbolic pointers unimplemented: {instr}")
            return [state]

        E = state.expr_manager()
        p = instr.predicate()
        if mo1id == mo2id:
            state.set(
                instr,
                self.compare_values(
                    E, p, p1.offset(), p2.offset(), instr.is_unsigned()
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
            else:
                state.set(instr, ConcreteBool(p == Cmp.NE))
                state.pc = state.pc.get_next_inst()
            return [state]

        state.set_killed("Invalid pointer comparison")
        return [state]

    def compare_ptr_and_nonptr(self, em, pred, op1, op2):
        if pred not in (Cmp.EQ, Cmp.NE):
            return None  # we cannot handle that yet
        if dom_is_concrete(op1):
            op1, op2 = op2, op1
        assert op1.is_pointer()
        assert dom_is_concrete(op2)
        if op2.is_zero():
            obj, off = op1.object(), op1.offset()
            expr = em.And(
                em.Eq(obj, slowbeast.domains.concrete.ConcreteVal(0, obj.bitwidth())),
                em.Eq(off, slowbeast.domains.concrete.ConcreteVal(0, off.bitwidth())),
            )
            return expr if pred == Cmp.EQ else em.Not(expr)
        return None

    def exec_cmp(self, state, instr: Cmp):
        assert isinstance(instr, Cmp), instr
        assert instr.type().is_bool(), instr
        seval = state.eval
        getop = instr.operand
        op1 = seval(getop(0))
        op2 = seval(getop(1))
        assert _types_check(instr, op1, op2)

        op1isptr = op1.is_pointer()
        op2isptr = op2.is_pointer()
        if op1isptr or op2isptr:
            if op1isptr and op2isptr:
                return self.compare_pointers(state, instr, op1, op2)
            else:
                # we handle only comparison of symbolic constant (pointer) to
                # null
                expr_mgr = state.expr_manager()
                if op1isptr and op1.is_null():
                    state.set(
                        instr,
                        self.compare_values(
                            expr_mgr,
                            instr.predicate(),
                            expr_mgr.ConcreteVal(0, op1.bitwidth()),
                            op2,
                            instr.is_unsigned(),
                        ),
                    )
                elif op2isptr and op2.is_null():
                    state.set(
                        instr,
                        self.compare_values(
                            expr_mgr,
                            instr.predicate(),
                            op1,
                            expr_mgr.ConcreteVal(0, op1.bitwidth()),
                            instr.is_unsigned(),
                        ),
                    )
                else:
                    expr = self.compare_ptr_and_nonptr(
                        expr_mgr, instr.predicate(), op1, op2
                    )
                    if expr is None:
                        state.set_killed(
                            f"Comparison of pointer to this constant not implemented: {op1} cmp {op2}"
                        )
                        return [state]
                    state.set(instr, expr)
                state.pc = state.pc.get_next_inst()
                return [state]

        x = self.compare_values(
            state.expr_manager(),
            instr.predicate(),
            op1,
            op2,
            instr.is_unsigned(),
        )
        state.set(instr, x)
        state.pc = state.pc.get_next_inst()

        return [state]

    def _resolve_function_pointer(self, state, funptr):
        ptr = state.try_eval(funptr)
        if ptr is None:
            return None
        # FIXME: should we use a pointer instead of funs id?
        if not isinstance(ptr, ConcreteVal):
            return None

        for f in self._program:
            if f.get_id() == ptr.value():
                return f
        return None

    def exec_call(self, state, instr: Call):
        assert isinstance(instr, Call)
        fun = instr.called_function()
        if not isinstance(fun, Function):
            fun = self._resolve_function_pointer(state, fun)
            if fun is None:
                state.set_killed(
                    f"Failed resolving function pointer: {instr.called_function()}"
                )
                return [state]
            assert isinstance(fun, Function)

        if self.is_error_fn(fun):
            state.set_error(AssertFailError(f"Called '{fun.name()}'"))
            return [state]

        if fun.is_undefined():
            name = fun.name()
            if name == "abort":
                state.set_terminated("Aborted via an abort() call")
                return [state]
            if name in ("exit", "_exit"):
                state.set_exited(state.eval(instr.operand(0)))
                return [state]
            if name in unsupported_funs:
                state.set_killed(f"Called unsupported function: {name}")
                return [state]
            # NOTE: this may be overridden by child classes
            return self.exec_undef_fun(state, instr, fun)

        if self.calls_forbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.set_killed(f"calling '{fun.name()}', but calls are forbidden")
            return [state]

        return self.call_fun(state, instr, fun)

    def call_fun(self, state, instr, fun):
        # map values to arguments
        assert len(instr.operands()) == len(fun.arguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.arguments(), instr.operands())
        }
        state.push_call(instr, fun, mapping)
        return [state]

    def exec_undef_fun(self, state, instr, fun):
        retTy = fun.return_type()
        if retTy:
            if self.get_options().concretize_nondets:
                val = ConcreteVal(getrandbits(32), retTy)
            elif self._input_vector:
                val = self._input_vector.pop()
                ldbgv(f"Using value from input vector: {0}", (val,))
                assert val.type() == retTy, f"{val.type()} != {retTy}"
                # if assertions are turned off, just return nondet-value
                if val.type() != retTy:
                    dbg(
                        f"Input value type does not match ({val.type()} != {retTy}). "
                        "Using nondet value"
                    )
                    val = state.solver().fresh_value(fun.name(), retTy)
            else:
                val = state.solver().fresh_value(fun.name(), retTy)
                state.create_nondet(instr, val)
            state.set(instr, val)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_binary_op(self, state, instr: BinaryOperation):
        assert isinstance(instr, BinaryOperation)
        seval = state.eval
        getop = instr.operand
        op1 = seval(getop(0))
        op2 = seval(getop(1))
        assert _types_check(instr, op1, op2)

        states = []
        # if one of the operands is a pointer,
        # lift the other to pointer too
        r = None
        expr_mgr = state.expr_manager()
        op1ptr = op1.is_pointer()
        op2ptr = op2.is_pointer()
        if op1ptr:
            if not op2ptr:
                r = add_pointer_with_constant(expr_mgr, op1, op2)
            else:
                state.set_killed(f"Arithmetic on pointers not implemented yet: {instr}")
                return [state]
        elif op2ptr:
            if not op1ptr:
                r = add_pointer_with_constant(expr_mgr, op2, op1)
            else:
                state.set_killed(f"Arithmetic on pointers not implemented yet: {instr}")
                return [state]
        else:
            opcode = instr.operation()
            if opcode == BinaryOperation.ADD:
                r = expr_mgr.Add(op1, op2)
            elif opcode == BinaryOperation.SUB:
                r = expr_mgr.Sub(op1, op2)
            elif opcode == BinaryOperation.MUL:
                r = expr_mgr.Mul(op1, op2)
            elif opcode == BinaryOperation.DIV:
                if op1.is_float():
                    # compilers allow division by FP 0
                    r = expr_mgr.Div(op1, op2, instr.is_unordered())
                else:
                    good, bad = self.fork(
                        state, expr_mgr.Ne(op2, ConcreteVal(0, op2.type()))
                    )
                    if good:
                        state = good
                        assert not op1.is_float()
                        r = expr_mgr.Div(op1, op2, instr.is_unsigned())
                    if bad:
                        bad.set_killed("Division by 0")
                        states.append(bad)
                        if good is None:
                            return states
            elif opcode == BinaryOperation.SHL:
                r = expr_mgr.Shl(op1, op2)
            elif opcode == BinaryOperation.LSHR:
                r = expr_mgr.LShr(op1, op2)
            elif opcode == BinaryOperation.ASHR:
                r = expr_mgr.AShr(op1, op2)
            elif opcode == BinaryOperation.REM:
                r = expr_mgr.Rem(op1, op2, instr.is_unsigned())
            elif opcode == BinaryOperation.AND:
                r = expr_mgr.And(op1, op2)
            elif opcode == BinaryOperation.OR:
                r = expr_mgr.Or(op1, op2)
            elif opcode == BinaryOperation.XOR:
                r = expr_mgr.Xor(op1, op2)
            else:
                state.set_killed(f"Not implemented binary operation: {instr}")
                return [state]

        assert r, "Bug in creating a binary op expression"

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        states.append(state)
        return states

    def exec_ite(self, state, instr):
        cond = condition_to_bool(state.eval(instr.condition()), state.expr_manager())
        assert cond.type().is_bool(), cond

        if cond.is_concrete():
            cval = cond.value()
            if cval is True:
                state.set(instr, state.eval(instr.operand(0)))
            elif cval is False:
                state.set(instr, state.eval(instr.operand(0)))
            else:
                raise RuntimeError(f"Invalid value of boolean condition: {cval}")
        else:
            op1 = state.eval(instr.operand(0))
            op2 = state.eval(instr.operand(1))
            assert _types_check(instr, cond, op1, op2)

            expr = state.expr_manager().Ite(cond, op1, op2)
            state.set(instr, expr)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_unary_op(self, state, instr: UnaryOperation):
        assert isinstance(instr, UnaryOperation)
        op1 = state.eval(instr.operand(0))
        assert _types_check(instr, op1)

        opcode = instr.operation()
        expr_mgr = state.expr_manager()
        if opcode == UnaryOperation.EXTEND:
            assert isinstance(instr, Extend), instr
            r = expr_mgr.Extend(op1, instr.bitwidth(), not instr.is_signed())
        elif opcode == UnaryOperation.CAST:
            r = expr_mgr.Cast(op1, instr.casttype())
            if r is None:
                state.set_killed(f"Unsupported/invalid cast: {instr}")
                return [state]
        elif opcode == UnaryOperation.EXTRACT:
            start, end = instr.range()
            r = expr_mgr.Extract(op1, start, end)
        elif opcode == UnaryOperation.NEG:
            r = expr_mgr.Neg(op1)
        elif opcode == UnaryOperation.ABS:
            r = expr_mgr.Abs(op1)
        elif opcode == UnaryOperation.FP_OP:
            r = expr_mgr.FpOp(instr.fp_operation(), op1)
            if r is None:
                state.set_killed(f"Unsupported FP operation: {instr}")
                return [state]
        else:
            state.set_killed(f"Unary instruction not implemented: {instr}")
            return [state]

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assume_expr(self, state, v):
        v = condition_to_bool(v, state.expr_manager())
        assert v.is_bool(), v
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            isunsat = not v.value()
        else:
            tmp = self.assume(state, v)
            isunsat = tmp is None

        if isunsat:
            state.set_terminated(f"Assumption unsat: {v} (!= True)")

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
                tmp = self.assume(state, v)
                isunsat = tmp is None

            if isunsat:
                state.set_terminated(f"Assumption unsat: {o} == {v} (!= True)")
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def exec_assert_expr(self, state, v, msg: str = ""):
        states = []
        assert v.is_bool()
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            if not v.value():
                state.set_error(AssertFailError(msg))
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                states.append(okBranch)
            if errBranch:
                errBranch.set_error(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def exec_assert(self, state, instr: Assert):
        assert isinstance(instr, Assert)
        o = instr.condition()
        msg = instr.msg()
        if not msg:
            msg = str(o)
        v = state.eval(o)
        states = []
        assert v.is_bool()
        if v.is_concrete():
            if v.value() != True:
                state.set_error(AssertFailError(msg))
            else:
                state.pc = state.pc.get_next_inst()
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                okBranch.pc = okBranch.pc.get_next_inst()
                states.append(okBranch)
            if errBranch:
                errBranch.set_error(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def concretize(self, state, val):
        if val.is_concrete():
            return val

        return state.solver().concretize(val, *state.constraints())
