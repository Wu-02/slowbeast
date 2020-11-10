from ..ir.instruction import *
from slowbeast.domains.value import Value
from ..ir.constants import ConcreteBool
from ..ir.pointer import Pointer
from ..core.executor import Executor as ConcreteExecutor
from ..solvers.expressions import is_symbolic
from ..util.debugging import dbgv
from ..core.errors import AssertFailError
from slowbeast.domains.concrete import ConcreteVal

from .memory import SymbolicMemoryModel
from .executionstate import SEState
from .statesset import StatesSet

from random import getrandbits


class SEStats:
    def __init__(self):
        # number of branch instructions
        self.branchings = 0
        # number of branch instructions where we forked
        self.branch_forks = 0
        # number of times we called fork()
        self.fork_calls = 0
        # number of times when the call to fork() forked the execution
        self.forks = 0


def addPointerWithConstant(E, op1, op2):
    return Pointer(op1.object(), E.Add(op1.offset(), op2))


def evalCond(state, cond):
    assert isinstance(cond, ValueInstruction) or cond.is_concrete()
    E = state.getExprManager()
    c = state.eval(cond)
    assert isinstance(c, Value)
    # solvers make difference between bitvectors and booleans, so we must
    # take care of it here: if it is a bitvector, compare it to 0 (C
    # semantics)
    if c.is_concrete():
        cval = E.Ne(c, ConcreteVal(0, c.type()))
    else:
        assert is_symbolic(c)
        if not c.type().is_bool():
            assert c.type().bitwidth() == 1, "Invalid condition in branching"
            cval = E.Ne(c, ConcreteVal(0, c.type()))
        else:
            cval = c  # It already is a boolean expression

    return cval


class Executor(ConcreteExecutor):
    def __init__(self, solver, opts, memorymodel=None):
        if memorymodel is None:
            memorymodel = SymbolicMemoryModel(opts, solver)
        super(Executor, self).__init__(opts, memorymodel)
        self.solver = solver
        self.stats = SEStats()

    def is_error_fn(self, fun):
        if isinstance(fun, str):
            return fun in self.getOptions().error_funs
        return fun.getName() in self.getOptions().error_funs

    def error_funs(self):
        return self._error_funs

    def createState(self, pc=None, m=None):
        if m is None:
            m = self.getMemoryModel().createMemory()
        s = SEState(self, pc, m, self.solver)
        assert not s.getConstraints(), "the state is not clean"
        return s

    def createCleanState(self, pc=None, m=None):
        s = self.createState(pc, m)
        s.pushCall(None)
        return s

    def createStatesSet(self, S=None):
        ss = StatesSet(self.createCleanState())
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
                raise RuntimeError("Invalid condition: {0}".format(cond.value()))

        # check SAT of cond and its negation
        csat = state.is_sat(cond)
        if csat is None:
            T = state.copy()
            T.setKilled("Solver failure: {0}".format(r))

        ncond = state.getExprManager().Not(cond)
        ncsat = state.is_sat(ncond)
        if ncsat is None:
            F = state.copy()
            F.setKilled("Solver failure: {0}".format(r))

        # is one of the conditions implied?
        # in that case we do not need to add any constraint
        if csat is True and ncsat is False:
            return state, None
        elif ncsat is True and csat is False:
            return None, state
        else:
            if csat is True:
                T = state.copy()
                T.addConstraint(cond)

            if ncsat is True:
                F = state.copy()
                F.addConstraint(ncond)

            if T and F:
                self.stats.forks += 1

        return T, F

    # FIXME: make this a method of State?
    def assume(self, state, cond):
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
            state.addConstraint(cond)
            return state
        return None

    def execBranchTo(self, state, instr, to):
        """
        Execute a branch instruction and follow the given successor
        (True or False successor).
        """
        assert isinstance(instr, Branch)
        assert isinstance(to, bool)
        dbgv("branching to {0} succ of {1}".format(to, instr))
        self.stats.branchings += 1

        cond = instr.getCondition()
        cval = evalCond(state, cond)

        succ = None
        if to is True:
            s = self.assume(state, cval)
            succ = instr.getTrueSuccessor()
        elif to is False:
            s = self.assume(state, state.getExprManager().Not(cval))
            succ = instr.getFalseSuccessor()
        else:
            raise RuntimeError("Invalid branch successor: {0}".format(to))

        if s is None:
            dbgv("branching is not feasible!")
            return []
        else:
            assert succ
            s.pc = succ.instruction(0)

        return [s]

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        self.stats.branchings += 1

        cond = instr.getCondition()
        cval = evalCond(state, cond)

        trueBranch, falseBranch = self.fork(state, cval)
        # at least one must be feasable...
        assert trueBranch or falseBranch, "Fatal Error: failed forking condition"

        states = []
        if trueBranch:
            trueBranch.pc = instr.getTrueSuccessor().instruction(0)
            states.append(trueBranch)
        if falseBranch:
            falseBranch.pc = instr.getFalseSuccessor().instruction(0)
            states.append(falseBranch)

        if trueBranch and falseBranch:
            self.stats.branch_forks += 1

        return states

    def cmpValues(self, E, p, op1, op2, unsgn):
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

    def cmpPointers(self, state, instr, p1, p2):
        mo1 = p1.object()
        mo2 = p2.object()
        if is_symbolic(mo1) or is_symbolic(mo2):
            state.setKilled(
                "Comparison of symbolic pointers unimplemented: {0}".format(instr)
            )
            return [state]

        E = state.getExprManager()
        p = instr.getPredicate()
        if mo1.get_id() == mo2.get_id():
            state.set(
                instr,
                self.cmpValues(E, p, p1.offset(), p2.offset(), instr.isUnsigned()),
            )
            state.pc = state.pc.get_next_inst()
            return [state]
        else:
            if p != Cmp.EQ and p != Cmp.NE:
                state.setKilled(
                    "Comparison of pointers implemented only for "
                    "(non-)equality or into the same object"
                )
                return [state]
            else:
                state.set(instr, ConcreteBool(p == Cmp.NE))
                state.pc = state.pc.get_next_inst()
                return [state]

        raise RuntimeError("Invalid pointer comparison")

    def execCmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))

        if op1.is_pointer() or op2.is_pointer():
            if op1.is_pointer() and op2.is_pointer():
                return self.cmpPointers(state, instr, op1, op2)
            else:
                state.setKilled("Comparison of pointer to a constant not implemented")
                return state

        x = self.cmpValues(
            state.getExprManager(), instr.getPredicate(), op1, op2, instr.isUnsigned()
        )
        state.set(instr, x)
        state.pc = state.pc.get_next_inst()

        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        if self.is_error_fn(fun):
            state.setError(AssertFailError(f"Called '{fun.getName()}'"))
            return [state]

        if fun.isUndefined():
            return self.execUndefFun(state, instr, fun)

        if self.callsForbidden():
            # FIXME: make this more fine-grained, which calls are forbidden?
            state.setKilled(
                "calling '{0}', but calls are forbidden".format(fun.getName())
            )
            return [state]

        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {
            x: state.eval(y) for (x, y) in zip(fun.getArguments(), instr.getOperands())
        }
        state.pushCall(instr, fun, mapping)
        return [state]

    def execUndefFun(self, state, instr, fun):
        name = fun.getName()
        if name == "abort":
            state.setTerminated("Aborted via an abort() call")
            return [state]

        retTy = fun.getReturnType()
        if retTy:
            if self.getOptions().concretize_nondets:
                val = ConcreteVal(getrandbits(32), retTy)
            else:
                val = state.getSolver().freshValue(name, retTy.bitwidth())
            state.addNondet(val)
            state.set(instr, val)
        state.pc = state.pc.get_next_inst()
        return [state]

    def execBinaryOp(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        # if one of the operands is a pointer,
        # lift the other to pointer too
        r = None
        E = state.getExprManager()
        if op1.is_pointer():
            if not op2.is_pointer():
                r = addPointerWithConstant(E, op1, op2)
            else:
                state.setKilled(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr)
                )
                return [state]
        elif op2.is_pointer():
            if not op1.is_pointer():
                r = addPointerWithConstant(E, op2, op1)
            else:
                state.setKilled(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr)
                )
                return [state]
        else:
            if instr.getOperation() == BinaryOperation.ADD:
                r = E.Add(op1, op2)
            elif instr.getOperation() == BinaryOperation.SUB:
                r = E.Sub(op1, op2)
            elif instr.getOperation() == BinaryOperation.MUL:
                r = E.Mul(op1, op2)
            elif instr.getOperation() == BinaryOperation.DIV:
                r = E.Div(op1, op2, instr.isUnsigned())
            elif instr.getOperation() == BinaryOperation.SHL:
                r = E.Shl(op1, op2)
            elif instr.getOperation() == BinaryOperation.LSHR:
                r = E.LShr(op1, op2)
            elif instr.getOperation() == BinaryOperation.ASHR:
                r = E.AShr(op1, op2)
            elif instr.getOperation() == BinaryOperation.REM:
                r = E.Rem(op1, op2, instr.isUnsigned())
            elif instr.getOperation() == BinaryOperation.AND:
                r = E.And(op1, op2)
            elif instr.getOperation() == BinaryOperation.OR:
                r = E.Or(op1, op2)
            elif instr.getOperation() == BinaryOperation.XOR:
                r = E.Xor(op1, op2)
            else:
                state.setKilled("Not implemented binary operation: {0}".format(instr))
                return [state]

        assert r, "Bug in creating a binary op expression"

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def execUnaryOp(self, state, instr):
        assert isinstance(instr, UnaryOperation)
        op1 = state.eval(instr.getOperand(0))
        E = state.getExprManager()
        if instr.getOperation() == UnaryOperation.ZEXT:
            bw = instr.bitwidth()
            r = E.ZExt(op1, bw)
        elif instr.getOperation() == UnaryOperation.SEXT:
            bw = instr.bitwidth()
            r = E.SExt(op1, bw)
        elif instr.getOperation() == UnaryOperation.EXTRACT:
            start, end = instr.getRange()
            r = E.Extract(op1, start, end)
        elif instr.getOperation() == UnaryOperation.NOT:
            r = E.Not(op1)
        else:
            state.setKilled("Unary instruction not implemented: {0}".format(instr))
            return [state]

        state.set(instr, r)
        state.pc = state.pc.get_next_inst()
        return [state]

    def execAssumeExpr(self, state, v):
        assert v.is_bool()
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            isunsat = not v.value()
        else:
            tmp = self.assume(state, v)
            isunsat = tmp is None

        if isunsat:
            state.setTerminated("Assumption unsat: {0} == {1} (!= True)".format(o, v))

        return [state]

    def execAssume(self, state, instr):
        assert isinstance(instr, Assume)
        for o in instr.getOperands():
            v = state.eval(o)
            assert v.is_bool()
            if v.is_concrete():
                assert isinstance(v.value(), bool)
                isunsat = not v.value()
            else:
                tmp = self.assume(state, v)
                isunsat = tmp is None

            if isunsat:
                state.setTerminated(
                    "Assumption unsat: {0} == {1} (!= True)".format(o, v)
                )
                return [state]

        state.pc = state.pc.get_next_inst()
        return [state]

    def execAssertExpr(self, state, v, msg=""):
        states = []
        assert v.is_bool()
        if v.is_concrete():
            assert isinstance(v.value(), bool)
            if not v.value():
                state.setError(AssertFailError(msg))
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                states.append(okBranch)
            if errBranch:
                errBranch.setError(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def execAssert(self, state, instr):
        assert isinstance(instr, Assert)
        o = instr.getCondition()
        msg = instr.getMessage()
        if not msg:
            msg = str(o)
        v = state.eval(o)
        states = []
        assert v.is_bool()
        if v.is_concrete():
            if v.value() != True:
                state.setError(AssertFailError(msg))
            else:
                state.pc = state.pc.get_next_inst()
            states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                okBranch.pc = okBranch.pc.get_next_inst()
                states.append(okBranch)
            if errBranch:
                errBranch.setError(AssertFailError(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def toUnique(self, state, val):
        if val.is_concrete():
            return val

        return state.getSolver().toUnique(val, *state.getConstraints())

    def concretize(self, state, val):
        if val.is_concrete():
            return val

        return state.getSolver().concretize(val, *state.getConstraints())
