from .. symexe.symbolicexecution import SEOptions
from .. util.debugging import print_stderr, print_stdout, dbg

from . annotatedcfg import CFG, CFGPath
from .. analysis.dfs import DFSVisitor, DFSEdgeType
from . naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from . naivekindse import Result, KindSeOptions
from . inductionpath import InductionPath

from .. ir.instruction import Cmp

from copy import copy


class Relation:
    def __init__(self, pred, a, b, expr):
        self._pred = pred
        self.a = a
        self.b = b
        self.expr = expr

    def __eq__(self, rhs):
        return self._pred == rhs._pred and self.a == rhs.a and self.b == rhs.b

    def __str__(self):
        return "({0}) {1} ({2})".format(self.a, Cmp.predicateStr(self._pred),
                                        self.b)

class KindCFGPath:
    def __init__(self, cfgpath):
        self.cfgpath = cfgpath

    def newcfgpath(self, newpath):
        pathcopy = copy(self)
        pathcopy.cfgpath = newpath
        return pathcopy

class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions(),
            genannot=True):
        super(
            KindSymbolicExecutor,
            self).__init__(
            prog=prog,
            testgen=testgen,
            opts=opts)

        self.genannot = genannot
        self.cfgs = {}
        self.invpoints = []
        self.paths = []

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def executePath(self, path, fromInit=False):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        if fromInit:
            if not self.states:
                self.prepare()
            states = self.states
            assert states
            print_stdout(
                f"Executing init prefix: {path}", color="ORANGE")
            # we must execute without lazy memory
            executor = self.getExecutor()
        else:
            s = self.getIndExecutor().createState()
            s.pushCall(None, self.getProgram().getEntry())
            states = [s]
            executor = self.getIndExecutor()

            print_stdout(f"Executing prefix: {path}", color="ORANGE")

        assert states

        # execute the prefix of the path
        safe, unsafe = executor.executePath(states, path)
        self.stats.paths += 1

        # do one more step, i.e., execute one more block
        tmpstates = executor.executeTillBranch(safe)

        if fromInit:
            # include all unsafe states (even those that we gather
            # during the execution of the path, not only those that
            # reach the last point of the path)
            finalsafe, finalunsafe = [], unsafe
        else:
            finalsafe, finalunsafe = [], []

        for s in tmpstates:
            (finalunsafe, finalsafe)[s.isReady() or s.isTerminated()].append(s)

        return finalsafe, finalunsafe

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

    def extendPath(self, path, steps=-1, atmost=False):
        """
        Take a path and extend it by prepending one or more
        predecessors.

        \param steps     Number of predecessors to prepend.
                         Values less or equal to 0 have a special
                         meaning:
                           0  -> prepend until a join is find
                           -1 -> prepend until a branch is find
        \param atmost    if set to True, we allow to extend
                         less than the specified number of steps
                         if there are no predecessors.
                         If set to False, the path is dropped
                         if it cannot be extended (there are
                         not enough predecessors)
        """

        num = 0
        invpoints = self.invpoints
        newpaths = []
        cfgpath = path.cfgpath
        worklist = [cfgpath]
        while worklist:
            num += 1
            newworklist = []

            for p in worklist:
                front = p.first()
                preds = front.getPredecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    newpaths.append(path.newcfgpath(p))
                    continue

                for pred in preds:
                    # FIXME: do not do this prepend, we always construct a new list....
                    # rather do append and then execute in reverse order (do a reverse
                    # iterator?)
                    newpath = CFGPath([pred] + p.getLocations())

                    # if this is the initial path and we are not stepping by 1,
                    # we must add it too, otherwise we could miss such paths
                    # (note that this is not covered by 'predsnum == 0',
                    # because init may have predecessors)
                    added = False
                    if atmost and steps != 1 and self._is_init(pred):
                        added = True
                        newpaths.append(path.newcfgpath(newpath))

                    if pred in invpoints:
                        # a point for generating invariant, stop extending here
                        newpaths.append(path.newcfgpath(newpath))
                    elif steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    elif steps == -1 and pred.isBranch():
                        newworklist.append(newpath)
                    else:  # we're done with this path
                        if not added:
                            newpaths.append(path.newcfgpath(newpath))

            worklist = newworklist

        return newpaths

    def report(self, n):
        if n.hasError():
            print_stderr(
                "{0}: {1}, {2}".format(
                    n.getID(),
                    n.pc,
                    n.getError()),
                color='RED')
            self.stats.errors += 1
            return Result.UNSAFE
        elif n.wasKilled():
            print_stderr(
                n.getStatusDetail(),
                prefix='KILLED STATE: ',
                color='WINE')
            self.stats.killed_paths += 1
            return Result.UNKNOWN

        return None

    def getRelations(self, state):
        rels = []
        EM = state.getExprManager()

        # FIXME not efficient, just for testing now
        values = list(state.getValuesList())
        for i in range(0, len(values)):
            for j in range(i + 1, len(values)):
                val1 = state.get(values[i])
                val2 = state.get(values[j])

                if val1.getType() != val2.getType() or\
                   val1.isPointer() or val1.isBool():
                    continue

                # FIXME: do not compare exprs that has the same nondets...
                # FIXME: do some quick syntectic checks
                lt = EM.Lt(val1, val2)
                islt = state.is_sat(lt)
                expr = None
                pred = None
                if islt is False:  # val1 >= val2
                    gt = EM.Gt(val1, val2)
                    isgt = state.is_sat(gt)
                    if isgt is False:  # val1 <= val2
                        #print(val1, '=', val2)
                        expr = EM.Eq(val1, val2)
                        pred = Cmp.EQ
                    elif isgt is True:
                        #print(val1, '>=', val2)
                        expr = EM.Ge(val1, val2)
                        pred = Cmp.GE
                elif islt is True:
                    gt = EM.Gt(val1, val2)
                    isgt = state.is_sat(gt)
                    if isgt is False:
                        #print(val1, '<=', val2)
                        expr = EM.Le(val1, val2)
                        pred = Cmp.LE

                if expr and not expr.isConstant():
                    assert pred
                    rels.append(Relation(pred, values[i], values[j], expr))

        return rels

    def annotateCFG(self, path, safe, unsafe):
        """
        Take the executed path and states that are safe and unsafe
        and derive annotations of CFG
        """
        if not self.genannot: # we should not generate invariants
            return

        if not path.cfgpath.first() in self.invpoints:
            return

        for s in safe:
            print("--Constraints--")
            print(s.getConstraints())
            print("--Relations--")

            # filter out those relations that make the state safe
            saferels = (r for r in self.getRelations(s) if not all(u.is_sat(r.expr) for u in unsafe))

            for r in saferels:
                print(r)


    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            cfgpath = path.cfgpath
            first_loc = cfgpath.first()
            if self._is_init(first_loc):
                # try executing the CFG path from initial states
                safe, unsafe = self.executePath(cfgpath, fromInit=True)
                if not unsafe:
                    self.annotateCFG(path, safe, unsafe)
                    if len(first_loc.getPredecessors()) == 0:
                        # this path is safe and we do not need to extend it
                        continue
                    # else just fall-through to execution from clear state
                    # as we can still prolong this path
                else:
                    for n in unsafe:
                        # we found a real error or hit another problem
                        if n.hasError() or n.wasKilled():
                            return self.report(n)
                        else:
                            assert False, "Unhandled unsafe state"

            safe, unsafe = self.executePath(cfgpath)

            self.annotateCFG(path, safe, unsafe)

            step = self.getOptions().step
            for n in unsafe:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path,
                                                steps=step,
                                                atmost=step != 1)
                    break
                elif n.wasKilled():
                    return self.report(n)
                else:
                    assert False, "Unhandled Unsafe state"

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

    def findInvPoints(self, cfg):
        points = []

        def processedge(start, end, dfstype):
            if dfstype == DFSEdgeType.BACK:
                points.append(end)

        DFSVisitor().foreachedge(processedge, cfg.getEntry())

        return points

    def initializePaths(self, k=1):
        cfg = self.getCFG(self.getProgram().getEntry())

        self.invpoints = self.findInvPoints(cfg)

        nodes = cfg.getNodes()
        paths = [KindCFGPath(CFGPath([p])) for n in nodes
                 for p in n.getPredecessors()
                 if n.hasAssert()]
        step = self.getOptions().step
        while k > 0:
            paths = [
                np for p in paths for np in self.extendPath(
                    p, steps=step, atmost=True)]
            k -= 1

        return paths

    def run(self):
        dbg("Performing the k-ind algorithm only for the main function",
            color="ORANGE")

        k = 1

        self.paths = self.initializePaths()

        if len(self.paths) == 0:
            print_stdout("Found no error state!", color='GREEN')
            return 0

        while True:
            print_stdout("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r = self.checkPaths()
            if r is Result.SAFE:
                print_stdout(
                    "All possible error paths ruled out!",
                    color="GREEN")
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNSAFE:
                dbg("Error found.", color='RED')
                return 1
            elif r is Result.UNKNOWN:
                print_stdout("Hit a problem, giving up.", color='ORANGE')
                return 1
            else:
                assert r is None

            k += 1
