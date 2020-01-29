from .. util.debugging import dbg
from .. ir.instruction import *
from .. interpreter.executor import Executor as ConcreteExecutor


class Executor(ConcreteExecutor):
    def __init__(self, solver):
        super(ConcreteExecutor, self).__init__()
        self.solver = solver

    def fork(self, state, cond):
        E = self.solver.getExprManager()
        T, F = None, None
        # FIXME: use implication as in the original King's paper?
        formula = E.And(state.getPathCondition(), cond)
        if self.solver.is_sat(formula):
            T = state.copy()
            T.setPathCondition(formula)

        formula = E.And(state.getPathCondition(), E.Not(cond))
        if self.solver.is_sat(formula):
            F = state.copy()
            F.setPathCondition(formula)

        return T, F

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        c = instr.getCondition()
        assert isinstance(c, ValueInstruction) or c.isConstant()
        cval = state.eval(c)

        trueBranch, falseBranch = self.fork(state, cval)

        states = []
        if trueBranch:
            states.append(trueBranch)
            trueBranch.pc = instr.getTrueSuccessor().getInstruction(0)
        elif falseBranch:
            states.append(trueBranch)
            trueBranch.pc = instr.getFalseSuccessor().getInstruction(0)
        else:
            # at least one must be feasable...
            raise RuntimeError("Fatal Error: failed forking condition")

        return states

    def execCmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        if op1.isPointer() or op2.isPointer():
            raise NotImplementedError("Comparison of pointer unimplemented")
        # if op1.isPointer():
           # if not op2.isPointer():
           #    # TODO: not implemented
           #    raise ExecutionError("Comparison of pointer to a constant")
           # if op1.object.getID() != op2.object.getID():
           #    raise ExecutionError("Comparison of unrelated pointers")
           #op1 = op1.offset
           #op2 = op2.offset
        x = None
        E = self.solver.getExprManager()
        p = instr.getPredicate()
        if p == Cmp.LE:
            x = E.Le(op1, op2)
        elif p == Cmp.LT:
            x = E.Lt(op1, op2)
        elif p == Cmp.GE:
            x = E.Ge(op1, op2)
        elif p == Cmp.GT:
            x = E.Gt(op1, op2)
        elif p == Cmp.EQ:
            x = E.Eq(op1, op2)
        elif p == Cmp.NE:
            x = E.Ne(op1, op2)

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
            raise NotImplementedError("Arithmetic on pointer not implemented yet")
       #if op1c.isPointer():
       #    if not op2c.isPointer():
       #        assert isinstance(op2c, Constant)
       #        # adding a constant -- create a pointer
       #        # to the object with the right offset
       #        op2c = Pointer(op1c.object, op2c.getValue())
       #elif op2c.isPointer():
       #    if not op1c.isPointer():
       #        assert isinstance(op1c, Constant)
       #        # adding a constant -- create a pointer
       #        # to the object with the right offset
       #        op1c = Pointer(op2c.object, op1c.getValue())
       #else:
       #    op1 = op1c.getValue()
       #    op2 = op2c.getValue()

       #if op1c.isPointer() and op1c.object != op2c.object:
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


