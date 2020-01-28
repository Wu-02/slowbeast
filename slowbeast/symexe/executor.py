from .. util.debugging import dbg
from .. ir.instruction import *
from .. interpreter.executor import Executor as ConcreteExecutor

class Executor(ConcreteExecutor):
    def __init__(self, solver):
        super(ConcreteExecutor, self).__init__()
        self.solver = solver

    def execBranch(self, state, instr):
        print('Branch')
        assert isinstance(instr, Branch)
        c = instr.getCondition()
        assert isinstance(c, ValueInstruction) or c.isConstant()
        cv = state.eval(instr.getCondition()).value

        if cv == True:
            succ = instr.getTrueSuccessor()
        elif cv == False:
            succ = instr.getFalseSuccessor()
        else:
            raise ExecutionError("Indeterminite condition")

        assert succ
        if not succ.empty():
            state.pc = succ.getInstruction(0)
        else:
            state.pc = None

        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)
        fun = instr.getCalledFunction()
        dbg("-- CALL {0} --".format(fun.getName()))

        if fun.isUndefined():
            return self.execUndefFun(state, instr, fun)

        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x : state.eval(y) for (x, y)\
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

