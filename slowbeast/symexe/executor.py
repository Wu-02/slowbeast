from .. util.debugging import dbg
from .. ir.instruction import *
from .. ir.value import Value
from .. interpreter.executor import Executor as ConcreteExecutor
from .. solvers.expressions import is_symbolic


class SEStats:
    def __init__(self):
        # number of branch instructions
        self.branchings = 0
        # number of branch instructions where we forked
        self.forks = 0


class Executor(ConcreteExecutor):
    def __init__(self, solver):
        super(ConcreteExecutor, self).__init__()
        self.solver = solver
        self.stats = SEStats()

    def fork(self, state, cond):
        E = self.solver.getExprManager()
        T, F = None, None

        # cond may be constant if the condition is concrete
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
        # FIXME: use implication as in the original King's paper?
        formula = E.And(state.getPathCondition(), cond)
        if self.solver.is_sat(formula):
            T = state.copy()
            T.setPathCondition(formula)

        formula = E.And(state.getPathCondition(), E.Not(cond))
        if self.solver.is_sat(formula):
            F = state.copy()
            F.setPathCondition(formula)

        if T and F:
            self.stats.forks += 1

        return T, F

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        self.stats.branchings += 1

        cond = instr.getCondition()
        assert isinstance(cond, ValueInstruction) or cond.isConstant()
        E = self.solver.getExprManager()
        c = state.eval(cond)
        assert isinstance(c, Value)
        # solvers make difference between bitvectors and booleans, so we must
        # take care of it here: if it is a bitvector, compare it to 0 (C
        # semantics)
        if c.isConstant():
            cval = E.Ne(c, E.Constant(0, c.getType().getBitWidth()))
        else:
            # It already is an boolean expression
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
        else:
            # at least one must be feasable...
            raise RuntimeError("Fatal Error: failed forking condition")

        return states

    def cmpValues(self, p, op1, op2):
        E = self.solver.getExprManager()
        if p == Cmp.LE:
            return E.Le(op1, op2)
        elif p == Cmp.LT:
            return E.Lt(op1, op2)
        elif p == Cmp.GE:
            return E.Ge(op1, op2)
        elif p == Cmp.GT:
            return E.Gt(op1, op2)
        elif p == Cmp.EQ:
            return E.Eq(op1, op2)
        elif p == Cmp.NE:
            return E.Ne(op1, op2)
        else:
            raise RuntimeError("Invalid comparison")

    def cmpPointers(self, state, instr, p1, p2):
        mo1 = p1.getObject()
        mo2 = p2.getObject()
        if is_symbolic(mo1) or is_symbolic(mo2):
            raise NotImplementedError(
                "Comparison of symbolic pointers unimplemented")

        E = self.solver.getExprManager()
        p = instr.getPredicate()
        if mo1.getID() == mo2.getID():
            state.set(instr, self.cmpValues(p, p1.getOffset(), p2.getOffset()))
            state.pc = state.pc.getNextInstruction()
            return [state]
        else:
            if p != Cmp.EQ and p != Cmp.NE:
                raise NotImplementedError(
                    "Comparison of pointers implemented only for "
                    "(non-)equality or into the same object")
            else:
                state.set(instr, Constant(p == Cmp.NE, BoolType()))
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
                raise NotImplementedError(
                    "Comparison of pointer to a constant not implemented")

        x = self.cmpValues(instr.getPredicate(), op1, op2)
        state.set(instr, x)
        state.pc = state.pc.getNextInstruction()

        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        dbg("-- CALL {0} --".format(fun.getName()))

        if fun.isUndefined():
            return self.execUndefFun(state, instr, fun)

        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x: state.eval(y) for (x, y)
                   in zip(fun.getArguments(), instr.getOperands())}
        state.pushCall(instr, fun, mapping)
        return [state]

    def execUndefFun(self, state, instr, fun):
        # FIXME: function must have a ret type to find out the
        # width of values...
        val = self.solver.freshValue(fun.getName(), 32)
        state.set(instr, val)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execBinaryOp(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        # if one of the operands is a pointer,
        # lift the other to pointer too
        if op1.isPointer() or op2.isPointer():
            raise NotImplementedError(
                "Arithmetic on pointer not implemented yet")
       # if op1c.isPointer():
       #    if not op2c.isPointer():
       #        assert isinstance(op2c, Constant)
       #        # adding a constant -- create a pointer
       #        # to the object with the right offset
       #        op2c = Pointer(op1c.object, op2c.getValue())
       # elif op2c.isPointer():
       #    if not op1c.isPointer():
       #        assert isinstance(op1c, Constant)
       #        # adding a constant -- create a pointer
       #        # to the object with the right offset
       #        op1c = Pointer(op2c.object, op1c.getValue())
       # else:
       #    op1 = op1c.getValue()
       #    op2 = op2c.getValue()

       # if op1c.isPointer() and op1c.object != op2c.object:
       #    raise ExecutionError("Pointer arithmetic on unrelated pointers")

        r = None
        E = self.solver.getExprManager()
        if instr.getOperation() == BinaryOperation.ADD:
            r = E.Add(op1, op2)
        elif instr.getOperation() == BinaryOperation.SUB:
            r = E.Sub(op1, op2)
        elif instr.getOperation() == BinaryOperation.MUL:
            r = E.Mul(op1, op2)
        elif instr.getOperation() == BinaryOperation.DIV:
            r = E.Div(op1, op2)
        else:
            raise NotImplementedError("Binary operation: " + str(instr))

        state.set(instr, r)
        state.pc = state.pc.getNextInstruction()
        return [state]
