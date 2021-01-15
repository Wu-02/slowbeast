from slowbeast.util.debugging import dbgv
from .executor import Executor as SExecutor
from .annotations import execute_annotations
from slowbeast.core.executor import (
    PathExecutionResult,
    split_ready_states,
    split_nonready_states,
)


class Executor(SExecutor):
    """
    Symbolic Executor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(self, solver, opts, memorymodel=None):
        super(Executor, self).__init__(solver, opts, memorymodel)

    def execute_annotations(self, states, annots):
        # if there are no annotations, return the original states
        if not annots:
            return states, []

        ready = []
        nonready = []

        for s in states:
            ts, tu = execute_annotations(self, s, annots)
            ready += ts
            nonready += tu
        return ready, nonready

    def _exec_assume_edge(self, states, edge):
        nonready = []
        isnot = edge.assume_false()
        for elem in edge:
            newstates = []
            for r in states:
                cond = r.get(elem)
                if cond is None:
                    r.setTerminated(f"Invalid assume edge: {elem}")
                    nonready.append(r)
                tmp = self.execAssumeExpr(
                    r, r.expr_manager().Not(cond) if isnot else cond
                )
                for t in tmp:
                    if t.isReady():
                        newstates.append(t)
                    else:
                        nonready.append(t)
            states = newstates

        return states, nonready

    def _execute_annotated_edge(self, states, edge, path):
        source = edge.source()
        ready, nonready = states, []
        # annotations before source
        locannot = path.annot_before_loc(source) if path else None
        if locannot:
            ready, tu = self.execute_annotations(ready, locannot)
            nonready += tu
        # annotations after source
        locannot = path.annot_after_loc(source) if path else None
        if locannot:
            ready, tu = self.execute_annotations(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_call() and not edge.called_function().isUndefined():
            fn = edge.called_function().name()
            for s in ready:
                s.setTerminated("Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        return ready, nonready

    def execute_annotated_path(self, state, path):
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
        edges = path.edges()

        # execute the precondition of the path
        pre = path.annot_before()
        if pre:
            states, tu = self.execute_annotations(states, pre)
            earlytermstates += tu

        pathlen = len(path)
        for idx in range(pathlen):
            edge = edges[idx]
            dbgv(f"vv ----- Edge {edge} ----- vv")
            states, nonready = self._execute_annotated_edge(states, edge, path)
            assert all(map(lambda x: x.isReady(), states))
            assert all(map(lambda x: not x.isReady(), nonready))

            # now execute the branch following the edge on the path
            if idx < pathlen - 1:
                earlytermstates += nonready
            else:  # this is the last edge on the path,
                errors, other = split_nonready_states(nonready)
                errors, other = errors or [], other or []
                # execute the annotations of the target (as _execute_annotated_edge
                # executes only the annotations of the source to avoid repetition)
                target = edge.target()
                locannot = path.annot_before_loc(target)
                if locannot and states:
                    states, tu = self.execute_annotations(states, locannot)
                    err, oth = split_nonready_states(tu)
                    if err: errors.extend(err)
                    if oth: other.extend(oth)
                if locannot and states:
                    states, tu = self.execute_annotations(states, locannot)
                    err, oth = split_nonready_states(tu)
                    if err: errors.extend(err)
                    if oth: other.extend(oth)
                # execute the postcondition of the path
                post = path.annot_after()
                if post and states:
                    states, tu = self.execute_annotations(states, post)
                    err, oth = split_nonready_states(tu)
                    if err: errors.extend(err)
                    if oth: other.extend(oth)

                result.errors = errors or None
                result.other = other or None

            dbgv(f"^^ ----- Edge {edge} ----- ^^")
            if not states:
                break

        result.ready = states or None
        result.early = earlytermstates or None

        assert result.check(), "The states were partitioned incorrectly"
        return result


class CFGExecutor(SExecutor):
    """
    Symbolic Executor instance adjusted to executing
    paths possibly annotated with formulas.
    The paths are supposed to be AnnotatedCFGPaths (paths in CFG)
    """

    def __init__(self, solver, opts, memorymodel=None):
        super(Executor, self).__init__(solver, opts, memorymodel)

    def executeAnnotations(self, states, annots):
        # if there are no annotations, return the original states
        if not annots:
            return states, []

        ready = []
        nonready = []

        for s in states:
            ts, tu = execute_annotations(self, s, annots)
            ready += ts
            nonready += tu
        return ready, nonready

    def executeAnnotatedLoc(self, states, loc, path=None):
        dbgv(f"vv ----- Loc {loc.bblock().get_id()} ----- vv")

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

        dbgv(f"^^ ----- Loc {loc.bblock().get_id()} ----- ^^")
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
        newpc = locs[0].bblock().first()
        for s in states:
            s.pc = newpc

        # execute the precondition of the path
        pre = path.getPrecondition()
        if pre:
            states, tu = self.executeAnnotations(states, pre)
            earlytermstates += tu

        locsnum = len(locs)
        for idx in range(0, locsnum):
            loc = locs[idx]
            ready, nonready = self.executeAnnotatedLoc(states, loc, path)
            assert all(map(lambda x: x.isReady(), ready))
            assert all(map(lambda x: isinstance(x.pc, Branch), ready)), [
                s.pc for s in ready
            ]

            # now execute the branch following the edge on the path
            if idx < locsnum - 1:
                earlytermstates += nonready

                # if this is the last edge and we should branch, do it
                if branch_on_last and idx == locsnum - 2:
                    newstates = self.executeTillBranch(ready)
                    assert all(map(lambda x: x.isReady(), newstates))
                else:
                    curbb = loc.bblock()
                    succbb = locs[idx + 1].bblock()
                    followsucc = curbb.last().true_successor() == succbb
                    newstates = []
                    assert followsucc or curbb.last().false_successor() == succbb
                    for s in ready:
                        newstates += self.execBranchTo(s, s.pc, followsucc)
            else:  # this is the last location on path,
                # so just normally execute the branch instruction in the block
                newstates = self.executeTillBranch(ready)
                # we executed only the branch inst, so the states still must be
                # ready
                assert all(map(lambda x: x.isReady(), newstates))
                assert not result.errors, "Have unsafe states before the last location"
                result.errors, result.other = split_nonready_states(nonready)
            states = newstates
            if not states:
                break

        # execute the postcondition of the path
        post = path.getPostcondition()
        if post:
            states, tu = self.executeAnnotations(states, post)
            result.errors, result.other = split_nonready_states(tu)

        result.ready = states or None
        result.early = earlytermstates or None

        assert result.check(), "The states were partitioned incorrectly"
        return result


# def substitute_constraints(constr, EM, prex, x):
#     newC = []
#     # FIXME: we need to do that at once!
#     for c in constr:
#         expr = EM.substitute(c, (x, prex))
#         if expr.is_concrete():
#             if expr.value() is False:
#                 return None  # infeasible constraints
#             elif expr.value() is not True:
#                 raise RuntimeError(f"Invalid constraint: {expr}")
#         else:
#             newC.append(expr)
#     return newC

# def joinStates(self, fromstates, tostates):
#    dbg_sec("Joining states")
#    # join the states
#    finalstates = []
#    for r in fromstates:
#        EM = r.expr_manager()
#        for s in tostates:
#            tmpr = r.copy()
#            newconstr = s.getConstraints()

#            FIXME("Handle other nondets")  # FIXME
#            # map constraints from s to r
#            for x in (l for l in s.getNondets() if l.isNondetLoad()):
#                prex = tmpr.get(x.load)
#                if not prex:
#                    res = self.execute(tmpr, x.load)
#                    assert len(res) == 1 and res[0] is tmpr
#                    prex = tmpr.get(x.load)
#                assert prex, "Do not have the value for x in pre-state"
#                if EM.equals(prex, x):
#                    continue  # no substitution needed
#                newconstr = substitute_constraints(newconstr, EM, prex, x)
#                if newconstr is None:
#                    tmpr = None
#                    break

#            if tmpr:
#                tmpr.addConstraint(*newconstr)
#                feas = tmpr.isfeasible()
#                assert feas is not None, "Solver failure"
#                if feas is True:
#                    finalstates.append(tmpr)

#    dbg_sec()
#    return finalstates

# def preimage(self, fromstate, tostates, path):
#    """
#    Get the states that make the execution
#    of path from 'fromstate' end up in 'tostates'
#    (ignoring pc of tostates).
#    NOTE: modifies 'fromstates'.
#    NOTE: This method does not set registers and memory
#    to mimic the execution of path -> tostates,
#    so it is sutiable only for computing the pre-condition
#    (the PC) of such path.
#    """

#    # execute the given path/block from 'fromstates'
#    dbg_sec("Computing preimage")
#    r = self.executeAnnotatedPath(fromstate, path)
#    finalstates = self.joinStates(r.ready or [], tostates)

#    dbg_sec()
#    return finalstates

# def preimage(self, fromstates, tostates, blk):
#     """
#     Get the states that make the execution
#     of blk from 'fromstates' end up in 'tostates'.
#     NOTE: modifies 'fromstates'.
#     NOTE: This method does not set registers and memory
#     to mimic the execution of blk -> tostates,
#     so it is sutiable only for computing the pre-condition
#     (the PC) of such path.
#     """

#     # execute the given path/block from 'fromstates'
#     dbg_sec("Computing preimage")
#     ready = []
#     for s in fromstates:
#         s.pc = blk.first()
#         rdy = self.executeTillBranch(s)
#         for r in rdy:
#             if r.isReady():
#                 ready.append(r)

#     finalstates = self.joinStates(ready, tostates)

#     dbg_sec()
#     return finalstates

# def executeAnnotatedStepWithPrefix(self, state, prefix):
#    """
#    Execute the given path through CFG with annotations from the given
#    state and then do one more step in CFG.

#    Returns three lists of states.
#    The first list contains safe states reachable after executing the 'path'
#    and doing one more step in CFG.
#    The second list contains unsafe states reachable after executing the 'path'
#    and doing one more step in CFG.
#    The last list contains states that terminate (e.g., are killed or are error
#    states) during the execution of the path, but that does not reach the last
#    step.
#    """

#    r = self.executeAnnotatedPath(state, prefix)
#    r.errorsToEarly()
#    r.otherToEarly()

#    dbg("Prefix executed, executing one more step")

#    # execute the last step -- all unsafe states are now really unsafe
#    cfg = prefix[0].getCFG()
#    tmpready = []
#    nonready = []
#    if r.ready:
#        for s in r.ready:
#            # get the CFG node that is going to be executed
#            # (executeAnnotatedPath transferd the control to the right bblocks)
#            loc = cfg.getNode(s.pc.bblock())
#            ts, tu = self.executeAnnotatedLoc([s], loc, prefix)
#            tmpready += ts
#            nonready += tu

#    assert r.errors is None
#    assert r.other is None
#    r.errors, r.other = split_nonready_states(nonready)

#    dbg("Step executed, done.")
#    return r
