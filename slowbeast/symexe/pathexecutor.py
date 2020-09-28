from slowbeast.util.debugging import dbg, dbgv, dbg_sec
from . executor import Executor as SExecutor
from slowbeast.core.executor import PathExecutionResult, split_ready_states, split_nonready_states

from slowbeast.ir.instruction import Branch, Instruction
from copy import copy


class Load:
    __slots__ = ['load']

    def __init__(self, l):
        self.load = l

class Annotation:
    ASSUME = 1
    ASSERT = 2
    INSTRS = 3

    __slots__ = ['type']

    def __init__(self, ty):
        assert ty >= Annotation.ASSUME and ty <= Annotation.INSTRS
        self.type = ty

    def isInstrs(self):
        return self.type == Annotation.INSTRS

    def isAssume(self):
        return self.type == Annotation.ASSUME

    def isAssert(self):
        return self.type == Annotation.ASSERT
        
class InstrsAnnotation(Annotation):
    """
    Annotation that is barely a sequence of instructions
    that should be executed
    """
    __slots__ = ['instrs']

    def __init__(self, instrs):
        super(InstrsAnnotation, self).__init__(Annotation.INSTRS)
        self.instrs = instrs

    def getInstructions(self):
        return self.instrs

    def __iter__(self):
        return self.instrs.__iter__()

    def __repr__(self):
        return "[{0}]".format(", ".join(map(lambda i: i.asValue(), self.instrs)))
 

def _createCannonical(expr, subs, EM):
    for (x, val) in subs.items():
        expr = EM.substitute(expr, (val, EM.Var(x.asValue(), val.getBitWidth())))
    return expr

class ExprAnnotation(Annotation):
    """
    Annotation that asserts (assumes) that an expression
    over the state holds
    """

    __slots__ = ['expr', 'subs', 'cannonical']

    def __init__(self, ty, expr, subs, EM):
        super(ExprAnnotation, self).__init__(ty)
        # the expression to evaluate
        self.expr = expr

        # substitution for the expression -
        # a mapping expr -> instruction meaning that
        # state.eval(instruction) should be put on the
        # place of the key expression
        assert isinstance(subs, dict)
        assert all(map(lambda k: isinstance(k, Instruction), subs.keys()))
        self.subs = subs

        # cannonical form of the annotation (so that we can compare
        # annotations)
        self.cannonical = _createCannonical(expr, subs, EM)

    def getExpr(self):
        return self.expr

    def getSubstitutions(self):
        return self.subs

    def getCannonical(self):
        return self.cannonical

    def Not(self, EM):
        n = copy(self)
        n.expr = EM.Not(self.expr)
        return n

    def doSubs(self, state):
        """
        Return the expression after substitutions
        in the given state
        """
        EM = state.getExprManager()
        get = state.get
        expr = self.expr
        for (x, val) in self.subs.items():
            curval = get(x)
            expr = EM.substitute(expr, (val, curval))
        return expr

    def __eq__(self, rhs):
        return self.cannonical == rhs.cannonical

    def __hash__(self):
        assert self.cannonical
        return self.cannonical.__hash__()

    def __repr__(self):
        assert self.cannonical
        return f"{self.cannonical}"
        #return "{0}[{1}]".format(self.expr, ", ".join(f"{x.asValue()}/{val.unwrap()}" for (x, val) in self.subs.items()))

class AssumeAnnotation(ExprAnnotation):
    def __init__(self, expr, subs, EM):
        super(AssumeAnnotation, self).__init__(Annotation.ASSUME, expr, subs, EM)

    def __repr__(self):
        return f"assume {ExprAnnotation.__repr__(self)}"

class AssertAnnotation(ExprAnnotation):
    def __init__(self, expr, subs, EM):
        super(AssertAnnotation, self).__init__(Annotation.ASSERT, expr, subs, EM)

    def toAssume(self, EM):
        return AssumeAnnotation(self.expr, self.subs, EM)

    def __repr__(self):
        return f"assert {ExprAnnotation.__repr__(self)}"

class Executor(SExecutor):
    """
    Symbolic Executor instance adjusted to executing
    paths with possibly annotated with formulas.
    """
    def __init__(self, solver, opts, memorymodel=None):
        super(Executor, self).__init__(solver, opts, memorymodel)

    def _executeAnnotation(self, states, annot, oldpc):
        dbg_sec(f"executing annotation: {annot}")

        def executeInstr(stts, instr):
            newstates = []
            for state in stts:
                assert state.isReady()
                # FIXME: get rid of this -- make execute() not to mess with pc
                state.pc = oldpc
                newstates += self.execute(state, instr)

            ready, nonready = [], []
            for x in newstates:
                x.pc = oldpc
                (ready, nonready)[0 if x.isReady() else 1].append(x)
            return ready, nonready

        assert all(map(lambda s: s.isReady(), states))

        ready, nonready = states, []
        if annot.isInstrs():
            for instr in annot:
                ready, u = executeInstr(ready, instr)
                nonready += u
        else:
            assert annot.isAssume() or annot.isAssert()
            subs = annot.getSubstitutions()
            for k in subs.keys():
                ready, nr = executeInstr(ready, k)
                nonready += nr

            isassume = annot.isAssume()
            expr = annot.getExpr()
            states = []
            for s in ready:
               #EM = s.getExprManager()
               #for (x, val) in subs.items():
               #    curval = s.get(x)
               #    expr = EM.substitute(expr, (val, curval))
                expr = annot.doSubs(s)
                if isassume:
                    dbg(f"assume {expr}")
                    states += self.execAssumeExpr(s, expr)
                else:
                    assert annot.isAssert()
                    dbg(f"assert {expr}")
                    tr, tu = split_ready_states(self.execAssertExpr(s, expr))
                    states += tr
                    nonready += tu
        dbg_sec()
        assert all(map(lambda s: s.pc is oldpc, states))
        return states, nonready

    def _executeAnnotations(self, s, annots):
        assert s.isReady(), "Cannot execute non-ready state"
        oldpc = s.pc

        dbg_sec(f"executing annotation on state {s.getID()}")

        ready, nonready = [s], []
        execAn = self._executeAnnotation
        for annot in annots:
            assert isinstance(annot, Annotation), annot
            ready, nr = execAn(ready, annot, oldpc)
            nonready += nr

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

    def executeAnnotatedPath(self, state, path, branch_on_last=False):
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

        If branch_on_last is set to True, instead of transfering control
        to the specified last point after executing all the previous points,
        normal fork is done (if there are multiple successors).
        That is, generate also states that avoid the last point
        at the path in one step.
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

        locsnum = len(locs)
        for idx in range(0, locsnum):
            loc = locs[idx]
            ready, nonready = self.executeAnnotatedLoc(states, loc, path)
            assert all(map(lambda x: x.isReady(), ready))
            assert all(map(lambda x: isinstance(x.pc, Branch), ready)), [
                s.pc for s in ready]

            # now execute the branch following the edge on the path
            if idx < locsnum - 1:
                earlytermstates += nonready

                # if this is the last edge and we should branch, do it
                if branch_on_last and idx == locsnum - 2:
                    newstates = self.executeTillBranch(ready)
                    assert all(map(lambda x: x.isReady(), newstates))
                else:
                    curbb = loc.getBBlock()
                    succbb = locs[idx + 1].getBBlock()
                    followsucc = curbb.last().getTrueSuccessor() == succbb
                    newstates = []
                    assert followsucc or curbb.last().getFalseSuccessor() == succbb
                    for s in ready:
                        newstates += self.execBranchTo(s, s.pc, followsucc)
            else:  # this is the last location on path,
                # so just normally execute the branch instruction in the block
                newstates = self.executeTillBranch(ready)
                # we executed only the branch inst, so the states still must be ready
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

