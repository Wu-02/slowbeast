import sys
from .. util.debugging import dbg, dbg_sec, FIXME
from .. ir.instruction import *
from .. ir.value import *
from . errors import GenericError
from . memorymodel import MemoryModel
from . executionstate import ExecutionState


def split_ready_states(states):
    ready, notready = [], []
    for x in states:
        (ready, notready)[0 if x.isReady() else 1].append(x)
    return ready, notready

def split_nonready_states(states):
    errs, oth = [], []
    for x in states:
        (errs, oth)[0 if x.hasError() else 1].append(x)
    return errs or None, oth or None

class PathExecutionResult:
    __slots__ = ['ready', 'errors', 'early', 'other']

    def __init__(self, ready=None, errors=None, early=None, other=None):
        # states that can be further executed
        self.ready = ready
        # error states that were hit during the execution
        # of the last point on the path
        self.errors = errors
        # non-ready states that were hit during the execution
        # of the path up to the last point
        # (these include error, terminated and killed states)
        self.early = early
        # other states --  these can be only the
        # killed and terminated states hit during the execution
        # of the last point on the path
        self.other = other

    def errorsToEarly(self):
        errs = self.errors
        earl = self.early
        if earl and errs:
            earl += errs
        elif errs:
            self.early = errs
        self.errors = None

    def otherToEarly(self):
        oth = self.other
        earl = self.early
        if earl and oth:
            earl += oth
        elif oth:
            self.early = oth
        self.other = None

    def check(self):
        assert not self.ready or all(map(lambda x: x.isReady(), self.ready))
        assert not self.errors or all(map(lambda x: x.isError(), self.errors))
        assert not self.early or all(map(lambda x: not x.isReady(), self.early))
        assert not self.other or all(map(lambda x: x.isTerminated() or x.isKilled(), self.other))
        return True


class Executor:
    """
    Class that takes care of executing single instructions.
    That is, the executor takes a state, executes one instruction
    and generates new states.
    """

    def __init__(self, opts, memorymodel=None):
        self.memorymodel = MemoryModel(
            opts) if memorymodel is None else memorymodel

        self._opts = opts
        self._executed_instrs = 0
        self._executed_blks = 0

    def getMemoryModel(self):
        assert self.memorymodel is not None
        return self.memorymodel

    def createState(pc=None, m=None):
        """
        Create a state that can be processed by this executor.
        """
        if m is None:
            m = self.memorymodel.createMemory()
        return ExecutionState(pc, m)

    def getExecInstrNum(self):
        return self._executed_instrs

    def getExecStepNum(self):
        return self._executed_blks

    def getOptions(self):
        return self._opts

    def forbidCalls(self):
        self._opts.no_calls = True

    def callsForbidden(self):
        return self._opts.no_calls

    def execStore(self, state, instr):
        assert isinstance(instr, Store)

        states = self.memorymodel.write(state,
                                        instr.getValueOperand(),
                                        instr.getPointerOperand())

        for s in states:
            if s.isReady():
                s.pc = s.pc.getNextInstruction()
        return states

    def execLoad(self, state, instr):
        assert isinstance(instr, Load)

        states = self.memorymodel.read(state, instr,
                                       instr.getPointerOperand(),
                                       instr.getBytesNum())

        for s in states:
            if s.isReady():
                s.pc = s.pc.getNextInstruction()
        return states

    def execAlloc(self, state, instr):
        states = self.memorymodel.allocate(state, instr)
        for s in states:
            if s.isReady():
                s.pc = s.pc.getNextInstruction()
        return states

    def execCmp(self, state, instr):
        assert isinstance(instr, Cmp)
        op1 = state.eval(instr.getOperand(0))
        op2 = state.eval(instr.getOperand(1))
        if op1.isPointer():
            if not op2.isPointer():
                raise RuntimeError("Comparison of pointer to a constant")
            if op1.object.getID() != op2.object.getID():
                raise RuntimeError("Comparison of unrelated pointers")
            op1 = op1.offset
            op2 = op2.offset
        else:
            op1 = op1.getValue()
            op2 = op2.getValue()
        x = None
        p = instr.getPredicate()
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

        state.set(instr, Constant(x, 1))
        state.pc = state.pc.getNextInstruction()

        return [state]

    def execPrint(self, state, instr):
        assert isinstance(instr, Print)
        for x in instr.getOperands():
            v = state.eval(x)
            if isinstance(v, Constant):
                v = v.getValue()
            sys.stdout.write(str(v))
        sys.stdout.write('\n')
        sys.stdout.flush()

        state.pc = state.pc.getNextInstruction()

        return [state]

    def execBranch(self, state, instr):
        assert isinstance(instr, Branch)
        c = instr.getCondition()
        assert isinstance(c, ValueInstruction) or c.isConstant()
        cv = state.eval(instr.getCondition()).getValue()

        if cv:
            succ = instr.getTrueSuccessor()
        elif cv == False:
            succ = instr.getFalseSuccessor()
        else:
            raise RuntimeError("Indeterminite condition")

        assert succ
        if not succ.empty():
            state.pc = succ.getInstruction(0)
        else:
            state.pc = None

        return [state]

    def execAssert(self, state, instr):
        assert isinstance(instr, Assert)
        for o in instr.getOperands():
            v = state.eval(o)
            assert isinstance(v, Constant)
            if v.getValue() != True:
                state.setError(
                    AssertFailError(
                        "Assertion failed: {0} is {1} (!= True)".format(
                            o, v)))
                return [state]

        state.pc = state.pc.getNextInstruction()
        return [state]

    def execAssume(self, state, instr):
        assert isinstance(instr, Assume)
        state.pc = state.pc.getNextInstruction()
        for o in instr.getOperands():
            v = state.eval(o)
            assert v.isConstant()
            assert v.isBool()
            if v.getValue() != True:
                print("Assumption failed: {0} == {1} (!= True)".format(o, v))
                state.dump()
                break

        return [state]

    def execUnaryOp(self, state, instr):
        raise NotImplementedError(
            "Concrete executor does not implement unary op yet")

    def execBinaryOp(self, state, instr):
        assert isinstance(instr, BinaryOperation)
        op1c = state.eval(instr.getOperand(0))
        op2c = state.eval(instr.getOperand(1))
        op1 = None
        op2 = None
        bw = max(op1c.getByteWidth(), op2c.getByteWidth())
        # if one of the operands is a pointer,
        # lift the other to pointer too
        if op1c.isPointer():
            if not op2c.isPointer():
                assert isinstance(op2c, Constant)
                # adding a constant -- create a pointer
                # to the object with the right offset
                op2c = Pointer(op1c.object, op2c.getValue())
        elif op2c.isPointer():
            if not op1c.isPointer():
                assert isinstance(op1c, Constant)
                # adding a constant -- create a pointer
                # to the object with the right offset
                op1c = Pointer(op2c.object, op1c.getValue())
        else:
            op1 = op1c.getValue()
            op2 = op2c.getValue()

        if op1c.isPointer() and op1c.object != op2c.object:
            raise RuntimeError("Pointer arithmetic on unrelated pointers")

        r = None
        if instr.getOperation() == BinaryOperation.ADD:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset + op2c.offset)
            else:
                r = Constant(op1 + op2, bw)
        elif instr.getOperation() == BinaryOperation.SUB:
            if isinstance(op1c, Pointer):
                assert isinstance(op2c, Pointer)
                r = Pointer(op1c.object, op1c.offset - op2c.offset)
            else:
                r = Constant(op1 - op2)
        elif instr.getOperation() == BinaryOperation.MUL:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset * op2c.offset)
            else:
                r = Constant(op1 * op2)
        elif instr.getOperation() == BinaryOperation.DIV:
            if op1c.isPointer():
                assert op2c.isPointer()
                r = Pointer(op1c.object, op1c.offset / op2c.offset)
            else:
                r = Constant(op1 / op2)
        else:
            raise NotImplementedError("Binary operation: " + str(instr))

        state.set(instr, r)
        state.pc = state.pc.getNextInstruction()
        return [state]

    def execCall(self, state, instr):
        assert isinstance(instr, Call)

        if self.callsForbidden():
            state.setKilled("Calls are forbidden")
            return [state]

        fun = instr.getCalledFunction()
        dbg("-- CALL {0} --".format(fun.getName()))
        if fun.isUndefined():
            state.setError(
                GenericError(
                    "Called undefined function: {0}".format(
                        fun.getName())))
            return [state]
        # map values to arguments
        assert len(instr.getOperands()) == len(fun.getArguments())
        mapping = {x: state.eval(y) for (x, y)
                   in zip(fun.getArguments(), instr.getOperands())}
        state.pushCall(instr, fun, mapping)
        return [state]

    def execRet(self, state, instr):
        assert isinstance(instr, Return)

        # obtain the return value (if any)
        ret = None
        if len(instr.getOperands()) != 0:  # returns something
            ret = state.eval(instr.getOperand(0))

        # pop the call frame and get the return site
        rs = state.popCall()
        if rs is None:  # popped the last frame
            if ret.isPointer():
                state.setError(
                    GenericError("Returning a pointer from main function"))
                return [state]
            elif not ret.isConstant():
                state.addWarning(
                    "Returning a non-constant value from the main function")

            state.setExited(ret)
            return [state]

        if ret:
            state.set(rs, ret)

        state.pc = rs.getNextInstruction()
        return [state]

    def execute(self, state, instr):
        """
        Execute the next instruction in the state and modify the state accordingly.
        If the instruction terminated the program, return the exit code.
        TODO: exceptional termination (like assert?)
        """
        # debug print
        dbg("({2}) {0}: {1}".format(
            '--' if not instr.getBBlock() else instr.getFunction().getName(),
            str(instr), state.getID()))

        self._executed_instrs += 1

        # TODO: add an opcode to instruction and check only the opcode
        states = None
        if isinstance(instr, Store):
            states = self.execStore(state, instr)
        elif isinstance(instr, Load):
            states = self.execLoad(state, instr)
        elif isinstance(instr, Alloc):
            states = self.execAlloc(state, instr)
        elif isinstance(instr, Cmp):
            states = self.execCmp(state, instr)
        elif isinstance(instr, Print):
            states = self.execPrint(state, instr)
        elif isinstance(instr, Branch):
            states = self.execBranch(state, instr)
        elif isinstance(instr, Assert):
            states = self.execAssert(state, instr)
        elif isinstance(instr, Assume):
            states = self.execAssume(state, instr)
        elif isinstance(instr, UnaryOperation):
            states = self.execUnaryOp(state, instr)
        elif isinstance(instr, BinaryOperation):
            states = self.execBinaryOp(state, instr)
        elif isinstance(instr, Call):
            states = self.execCall(state, instr)
        elif isinstance(instr, Return):
            states = self.execRet(state, instr)
        else:
            state.setKilled("Not implemented instruction: {0}".format(instr))
            return [state]

        return states

    def executeTillBranch(self, state, stopBefore=False):
        """
        Start executing from 'state' and stop execution after executing a
        branch instruction.  This usually will execute exactly one basic block
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

        while readystates:
            newst = []
            for s in readystates:
                # remember that it is a branch now,
                # because execute() will change pc
                isbranch = isinstance(s.pc, Branch)
                if stopBefore and isbranch:
                    finalstates.append(s)
                    continue

                nxt = self.execute(s, s.pc)
                if isbranch:
                    # we stop here
                    finalstates += nxt
                else:
                    for n in nxt:
                        if n.isReady():
                            newst.append(n)
                        else:
                            finalstates.append(n)

            readystates = newst

        assert not readystates
        return finalstates

    def executePath(self, state, path):
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

        locs = path.getLocations()
        # set the pc of the states to be the first instruction of the path
        for s in states:
            s.pc = locs[0].getBBlock().first()

        for idx in range(0, len(locs)):
            # execute the block till branch
            newstates = self.executeTillBranch(states, stopBefore=True)

            # get the ready states
            states = []
            for n in newstates:
                (states, earlytermstates)[0 if n.isReady else 1].append(n)

            # now execute the branch following the edge on the path
            if idx + 1 < len(locs):
                curbb = locs[idx].getBBlock()
                succbb = locs[idx + 1].getBBlock()
                followsucc = curbb.last().getTrueSuccessor() == succbb
                newstates = []
                assert followsucc or curbb.last().getFalseSuccessor() == succbb
                for s in states:
                    newstates += self.execBranchTo(s, s.pc, followsucc)
            else:  # this is the last location on path,
                # so just normally execute the block instructions
                newstates = self.executeTillBranch(states)
            states = newstates

        assert all(map(lambda x: x.isReady(), states))
        assert all(map(lambda x: not x.isReady(), earlytermstates))

        return states, earlytermstates

    def _executeAnnotations(self, s, annots):
        assert s.isReady(), "Cannot execute non-ready state"
        oldpc = s.pc

        def executeInstr(states, instr):
            newstates = []
            for state in states:
                assert s.isReady()
                # FIXME: get rid of this -- make execute() not to mess with pc
                state.pc = oldpc
                newstates += self.execute(state, instr)

            ready, nonready = [], []
            for x in newstates:
                x.pc = oldpc
                (ready, nonready)[0 if x.isReady() else 1].append(x)
            return ready, nonready

        ready, nonready = [s], []
        for annot in annots:
            dbg_sec(f"executing annotation on state {s.getID()}")
            for instr in annot:
                ready, u = executeInstr(ready, instr)
                nonready += u
            dbg_sec()
        return ready, nonready

    def executeAnnotations(self, states, annots):
        # if there are no annotations, return the original states
        if not annots:
            return states, []

        ready = []
        nonready = []
        execAnnot = self._executeAnnotations

        for s in states:
            ts, tu = execAnnot(s, annots)
            ready += ts
            nonready += tu
        return ready, nonready

    def executeAnnotatedLoc(self, states, loc, path=None):
        dbg(f"vv ----- Loc {loc.getBBlock().getID()} ----- vv")

        # execute annotations before bblock
        ready, nonready = self.executeAnnotations(states, loc.annotationsBefore)
        locannot = path.getLocAnnotationsBefore(loc) if path else None
        if locannot:
            ready, tu = self.executeAnnotations(ready, locannot)
            nonready += tu

        # execute the block till branch
        states = self.executeTillBranch(ready, stopBefore=True)

        # get the ready states
        ready, tmpnonready = split_ready_states(states)
        nonready += tmpnonready

        # execute annotations after
        ready, tmpnonready = self.executeAnnotations(ready, loc.annotationsAfter)
        nonready += tmpnonready

        locannot = path.getLocAnnotationsAfter(loc) if path else None
        if locannot:
            ready, tu = self.executeAnnotations(ready, locannot)
            nonready += tu

        dbg(f"^^ ----- Loc {loc.getBBlock().getID()} ----- ^^")
        return ready, nonready

    def executeAnnotatedPath(self, state, path):
        """
        Execute the given path through CFG with annotations from the given
        state. NOTE: the passed states may be modified.

        Return three lists of states.  The first list contains the states
        that reach the end of the path (i.e., the states after the execution of
        the last instruction on the path), the other list contains all other
        states, i.e., the error, killed or exited states reached during the
        execution of the CFG. Note that if the path is infeasible, this set
        contains no states.
        The last list contains states that terminate (e.g., are killed or are error
        states) during the execution of the path, but that does not reach the last
        step.
        """

        if isinstance(state, list):
            states = state
        else:
            states = [state]

        result = PathExecutionResult()

        earlytermstates = []
        idx = 0

        locs = path.getLocations()
        # set the pc of the states to be the first instruction of the path
        newpc = locs[0].getBBlock().first()
        for s in states:
            s.pc = newpc

        for idx in range(0, len(locs)):
            loc = locs[idx]
            ready, nonready = self.executeAnnotatedLoc(states, loc, path)
            assert all(map(lambda x: x.isReady(), ready))
            assert all(map(lambda x: isinstance(x.pc, Branch), ready)), [
                s.pc for s in ready]

            # now execute the branch following the edge on the path
            if idx + 1 < len(locs):
                curbb = loc.getBBlock()
                succbb = locs[idx + 1].getBBlock()
                followsucc = curbb.last().getTrueSuccessor() == succbb
                newstates = []
                assert followsucc or curbb.last().getFalseSuccessor() == succbb
                for s in ready:
                    newstates += self.execBranchTo(s, s.pc, followsucc)
                earlytermstates += nonready
            else:  # this is the last location on path,
                # so just normally execute the branch instruction in the block
                newstates = self.executeTillBranch(ready)
                # we executed only the branch inst, we the states still must be ready
                assert all(map(lambda x: x.isReady(), newstates))
                assert not result.errors, "Have unsafe states before the last location"
                result.errors, result.other = split_nonready_states(nonready)
            states = newstates

        result.ready = states or None
        result.early = earlytermstates or None

        assert result.check(), "The states were partitioned incorrectly"
        return result

    def executeAnnotatedStepWithPrefix(self, state, prefix):
        """
        Execute the given path through CFG with annotations from the given
        state and then do one more step in CFG.

        Returns three lists of states.
        The first list contains safe states reachable after executing the 'path'
        and doing one more step in CFG.
        The second list contains unsafe states reachable after executing the 'path'
        and doing one more step in CFG.
        The last list contains states that terminate (e.g., are killed or are error
        states) during the execution of the path, but that does not reach the last
        step.
        """

        r = self.executeAnnotatedPath(state, prefix)
        r.errorsToEarly()
        r.otherToEarly()

        dbg("Prefix executed, executing one more step")

        # execute the last step -- all unsafe states are now really unsafe
        cfg = prefix[0].getCFG()
        tmpready = []
        nonready = []
        if r.ready:
            for s in r.ready:
                # get the CFG node that is going to be executed
                # (executeAnnotatedPath transferd the control to the right bblocks)
                loc = cfg.getNode(s.pc.getBBlock())
                ts, tu = self.executeAnnotatedLoc([s], loc, prefix)
                tmpready += ts
                nonready += tu

        assert r.errors is None
        assert r.other is None
        r.errors, r.other = split_nonready_states(nonready)

        dbg("Step executed, done.")
        return r
