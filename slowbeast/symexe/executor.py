from .. util.debugging import dbg, FIXME
from .. ir.instruction import *
from .. ir.types import Type
from .. ir.value import Value, ConstantBool, Pointer, Constant
from .. interpreter.executor import Executor as ConcreteExecutor
from .. interpreter.memory import MemoryObject
from .. solvers.expressions import is_symbolic

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
    return Pointer(op1.getObject(), E.Add(op1.getOffset(), op2))


class Executor(ConcreteExecutor):
    def __init__(self, concretize_nondet=False):
        super(ConcreteExecutor, self).__init__()
        self.stats = SEStats()
        self._concretize_nondet = concretize_nondet

    def fork(self, state, cond):
        self.stats.fork_calls += 1

        T, F = None, None

        # fast path + do not add True/False to constraints
        if cond.isConstant():
            assert cond.isBool(), "Invalid constant"
            if cond.getValue():
                return state, None
            elif cond.getValue() == False:
                return None, state
            else:
                raise RuntimeError(
                    "Invalid condition: {0}".format(
                        cond.getValue()))
        # XXX use implication as in the original King's paper?
        if state.is_sat(cond):
            T = state.copy()
            T.addConstraint(cond)

        ncond = state.getExprManager().Not(cond)
        if state.is_sat(ncond):
            F = state.copy()
            F.addConstraint(ncond)

        if T and F:
            self.stats.forks += 1

        return T, F

    def assume(self, state, cond):
        """ Return a new states where we assume that condition is true.
            Return None if that situation cannot happen
        """
        if cond.isConstant():
            assert cond.isBool(), "Invalid constant"
            if cond.getValue():
                return state
            else:
                return None

        if state.is_sat(cond):
            T = state.copy()
            T.addConstraint(cond)
            return T
        return None

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        self.stats.branchings += 1

        cond = instr.getCondition()
        assert isinstance(cond, ValueInstruction) or cond.isConstant()
        E = state.getExprManager()
        c = state.eval(cond)
        assert isinstance(c, Value)
        # solvers make difference between bitvectors and booleans, so we must
        # take care of it here: if it is a bitvector, compare it to 0 (C
        # semantics)
        if c.isConstant():
            cval = E.Ne(c, E.Constant(0, c.getType().getBitWidth()))
        else:
            # It already is a boolean expression
            assert is_symbolic(c)
            assert c.getType().isBool()
            cval = c

        trueBranch, falseBranch = self.fork(state, cval)

        states = []
        if trueBranch:
            trueBranch.pc = instr.getTrueSuccessor().getInstruction(0)
            states.append(trueBranch)
        if falseBranch:
            falseBranch.pc = instr.getFalseSuccessor().getInstruction(0)
            states.append(falseBranch)
        # at least one must be feasable...
        assert trueBranch or falseBranch, "Fatal Error: failed forking condition"

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
        mo1 = p1.getObject()
        mo2 = p2.getObject()
        if is_symbolic(mo1) or is_symbolic(mo2):
            state.setKilled(
                "Comparison of symbolic pointers unimplemented: {0}".format(instr))
            return [state]

        E = state.getExprManager()
        p = instr.getPredicate()
        if mo1.getID() == mo2.getID():
            state.set(
                instr,
                self.cmpValues(E,
                               p,
                               p1.getOffset(),
                               p2.getOffset(),
                               instr.isUnsigned()))
            state.pc = state.pc.getNextInstruction()
            return [state]
        else:
            if p != Cmp.EQ and p != Cmp.NE:
                state.setKilled(
                    "Comparison of pointers implemented only for "
                    "(non-)equality or into the same object")
                return [state]
            else:
                state.set(instr, ConstantBool(p == Cmp.NE))
                state.pc = state.pc.getNextInstruction()
                return [state]

        raise RuntimeError("Invalid pointer comparison")

    def execCmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))

        if op1.isPointer() or op2.isPointer():
            if op1.isPointer() and op2.isPointer():
                return self.cmpPointers(state, instr, op1, op2)
            else:
                state.setKilled(
                    "Comparison of pointer to a constant not implemented")
                return state

        x = self.cmpValues(
            state.getExprManager(),
            instr.getPredicate(),
            op1,
            op2,
            instr.isUnsigned())
        state.set(instr, x)
        state.pc = state.pc.getNextInstruction()

        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        if fun.isUndefined():
            return self.execUndefFun(state, instr, fun)

        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x: state.eval(y) for (x, y)
                   in zip(fun.getArguments(), instr.getOperands())}
        state.pushCall(instr, fun, mapping)
        return [state]

    def execUndefFun(self, state, instr, fun):
        if fun.getName() == 'abort':
            state.setTerminated("Aborted via an abort() call")
            return [state]

        FIXME("Functions need return value type")
        retTy = fun.getReturnType()
        if retTy:
            if self._concretize_nondet:
                val = Constant(getrandbits(32), retTy)
            else:
                val = state.getSolver().freshValue(fun.getName(), retTy.getBitWidth())
            state.set(instr, val)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execBinaryOp(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        # if one of the operands is a pointer,
        # lift the other to pointer too
        r = None
        E = state.getExprManager()
        if op1.isPointer():
            if not op2.isPointer():
                r = addPointerWithConstant(E, op1, op2)
            else:
                state.setKilled(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr))
                return [state]
        elif op2.isPointer():
            if not op1.isPointer():
                r = addPointerWithConstant(E, op2, op1)
            else:
                state.setKilled(
                    "Arithmetic on pointers not implemented yet: {0}".format(instr))
                return [state]
        else:
            if instr.getOperation() == BinaryOperation.ADD:
                r = E.Add(op1, op2)
            elif instr.getOperation() == BinaryOperation.SUB:
                r = E.Sub(op1, op2)
            elif instr.getOperation() == BinaryOperation.MUL:
                r = E.Mul(op1, op2)
            elif instr.getOperation() == BinaryOperation.DIV:
                r = E.Div(op1, op2)
            elif instr.getOperation() == BinaryOperation.SHL:
                r = E.Shl(op1, op2)
            elif instr.getOperation() == BinaryOperation.LSHR:
                r = E.LShr(op1, op2)
            elif instr.getOperation() == BinaryOperation.ASHR:
                r = E.AShr(op1, op2)
            else:
                state.setKilled(
                    "Not implemented binary operation: {0}".format(instr))
                return [state]

        assert r, "Bug in creating a binary op expression"

        state.set(instr, r)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execUnaryOp(self, state, instr):
        assert isinstance(instr, UnaryOperation)
        op1 = state.eval(instr.getOperand(0))
        E = state.getExprManager()
        if instr.getOperation() == UnaryOperation.ZEXT:
            bw = instr.getBitWidth()
            r = E.ZExt(op1, bw)
        elif instr.getOperation() == UnaryOperation.SEXT:
            bw = instr.getBitWidth()
            r = E.SExt(op1, bw)
        elif instr.getOperation() == UnaryOperation.EXTRACT:
            start, end = instr.getRange()
            r = E.Extract(op1, start, end)
        else:
            state.setKilled(
                "Unary instruction not implemented: {0}".format(instr))
            return [state]

        state.set(instr, r)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execAssume(self, state, instr):
        assert isinstance(instr, Assume)
        for o in instr.getOperands():
            v = state.eval(o)
            assert v.isBool()
            if v.isConstant():
                if v.getValue() != True:
                    state.setTerminated(
                        "Assumption failed: {0} == {1} (!= True)".format(
                            o, v))
                    return [state]
                break
            else:
                state.addConstraint(v)

        state.pc = state.pc.getNextInstruction()
        return [state]

    def execAssert(self, state, instr):
        assert isinstance(instr, Assert)
        states = []
        o = instr.getCondition()
        msg = instr.getMessage()
        if not msg:
            msg = str(o)
        v = state.eval(o)
        assert v.isBool()
        if v.isConstant():
            if v.getValue() != True:
                state.setError("Assertion failed: {0}".format(msg))
                states.append(state)
        else:
            okBranch, errBranch = self.fork(state, v)
            if okBranch:
                okBranch.pc = okBranch.pc.getNextInstruction()
                states.append(okBranch)
            if errBranch:
                errBranch.setError("Assertion failed: {0}".format(msg))
                states.append(errBranch)

        assert states, "Generated no states"
        return states

    def toUnique(self, state, val):
        if val.isConstant():
            return val

        return state.getSolver().toUnique(val, *state.getConstraints())

    def concretize(self, state, val):
        if val.isConstant():
            return val

        return state.getSolver().concretize(val, *state.getConstraints())
