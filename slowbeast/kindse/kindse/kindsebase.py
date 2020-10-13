from slowbeast.util.debugging import print_stderr, print_stdout, dbg

from slowbeast.kindse.annotatedcfg import CFG
from slowbeast.analysis.callgraph import CallGraph
from slowbeast.symexe.symbolicexecution import SymbolicExecutor as SymbolicInterpreter, SEOptions
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.memory import LazySymbolicMemoryModel
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.transforms.splitbblocks import splitProgAroundCalls
from slowbeast.ir.instruction import Cmp


class KindSymbolicExecutor(SymbolicInterpreter):
    def __init__(
            self,
            prog,
            ohandler=None,
            opts=KindSeOptions()):
        super(
            KindSymbolicExecutor,
            self).__init__(
            P=prog,
            ohandler=ohandler,
            opts=opts,
            ExecutorClass=PathExecutor)

        # the executor for induction checks -- we need lazy memory access
        memorymodel = LazySymbolicMemoryModel(opts, self.getSolver())
        self.indexecutor = PathExecutor(self.getSolver(), opts, memorymodel)
        dbg("Forbidding calls in induction step for now with k-induction")
        self.indexecutor.forbidCalls()

        # run only on reachable functions
        callgraph = CallGraph(prog)
        if __debug__:
            with self.new_output_file('callgraph-full.txt') as f:
                callgraph.dump(f)

        callgraph.pruneUnreachable(prog.getEntry())
        if __debug__:
            with self.new_output_file('callgraph.txt') as f:
                callgraph.dump(f)

        self.callgraph = callgraph
        self.cfgs = {F: CFG(F)
                     for F in callgraph.getFunctions() if not F.isUndefined()}

        self.paths = []
        # as we run the executor in nested manners,
        # we want to give different outputs
        self.reportfn = print_stdout

        self.have_problematic_path = False

    def getIndExecutor(self):
        return self.indexecutor

    def getCFG(self, F):
        assert self.cfgs.get(F), f"Have no CFG for function {F.getName()}"
        return self.cfgs.get(F)

    def executePath(self, path, fromInit=False):
        """
        Execute the given path. The path is such that
        it ends one step before possible error.
        That is, after executing the path we must
        perform one more step to check whether the
        error is reachable
        """
        if fromInit:
            # we must execute without lazy memory
            executor = self.getExecutor()

            if not self.states:
                self.prepare()
            states = self.states
            assert states

            dbg(f"Executing (init) path: {path}",
                color="WHITE", fn=self.reportfn)
        else:
            executor = self.getIndExecutor()

            s = executor.createState()
            assert not s.getConstraints(), "The state is not clean"
            s.pushCall(None, self.getProgram().getEntry())
            states = [s]

            dbg(f"Executing path: {path}", color="WHITE", fn=self.reportfn)

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.executeAnnotatedPath(states, path, branch_on_last=True)
        self.stats.paths += 1

        earl = r.early
        if fromInit and earl:
            # this is an initial path, so every error is taken as real
            errs = r.errors or []
            for e in (e for e in earl if e.hasError()):
                errs.append(e)
            r.errors = errs

        return r

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

    def extendToCaller(self, path, states):
        self.have_problematic_path = True
        print_stdout("Killing a path that goes to caller")
       #start = path.first()
       #cgnode = self.callgraph.getNode(start.getBBlock().getFunction())
       # for callerfun, callsite in cgnode.getCallers():
       #    print('caller', callerfun.getFun())
       #    print('cs', callsite)
       #    callsite.getBBlock()
        return []

    def extendPath(self, path, states, steps=-1, atmost=False, stoppoints=[]):
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
        newpaths = []
        locs = path.getLocations()[:]
        locs.reverse()  # reverse the list so that we can do append
        worklist = [locs]
        while worklist:
            num += 1
            newworklist = []

            for p in worklist:
                front = p[-1]
                preds = front.getPredecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    if len(path) == len(p) and states:
                        # we did not extend the path at all, so this
                        # is a path that ends in the entry block and
                        # we already processed it...
                        dbg('Extending a path to the caller')
                        np = self.extendToCaller(path, states)
                        newpaths += np
                    else:
                        # FIXME: do not do this reverse, rather execute in reverse
                        # order (do a reverse iterator?)
                        p.reverse()
                        n = path.copyandsetpath(p)
                        newpaths.append(path.copyandsetpath(p))
                    continue

                for pred in preds:
                    newpath = p[:]
                    newpath.append(pred)

                    # if this is the initial path and we are not stepping by 1,
                    # we must add it too, otherwise we could miss such paths
                    # (note that this is not covered by 'predsnum == 0',
                    # because init may have predecessors)
                    added = False
                    if atmost and steps != 1 and self._is_init(pred):
                        added = True
                        tmp = newpath[:]
                        tmp.reverse()
                        newpaths.append(path.copyandsetpath(tmp))
                        # fall-through to further extending this path

                    assert all(map(lambda x: isinstance(x, CFG.AnnotatedNode),
                                   stoppoints))
                    if pred in stoppoints:
                        newpath.reverse()
                        newpaths.append(path.copyandsetpath(newpath))
                    elif steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    elif steps == -1 and pred.isBranch():
                        newworklist.append(newpath)
                    else:  # we're done with this path
                        if not added:
                            newpath.reverse()
                            newpaths.append(path.copyandsetpath(newpath))

            worklist = newworklist

        return newpaths

    def report(self, n, fn=print_stderr):
        if n.hasError():
            if fn:
                fn("state {0}: {1}, {2}".format(
                    n.getID(),
                    n.pc,
                    n.getError()),
                    color='RED')
            self.stats.errors += 1
            return Result.UNSAFE
        elif n.wasKilled():
            if fn:
                fn(n.getStatusDetail(),
                    prefix='KILLED STATE: ',
                    color='WINE')
            self.stats.killed_paths += 1
            return Result.UNKNOWN

        return None

    def checkInitialPath(self, path):
        """
        Execute a path from initial states
        \requires an initial path
        """

        r = self.executePath(path, fromInit=True)
        if not r.errors:
            killed = any(True for s in r.early if s.wasKilled()
                         ) if r.early else None
            if killed:
                return Result.UNKNOWN, r
            killed = any(True for s in r.other if s.wasKilled()
                         ) if r.other else None
            if killed:
                return Result.UNKNOWN, r
            if len(path.first().getPredecessors()) == 0:
                # this path is safe and we do not need to extend it
                return Result.SAFE, r
            # else just fall-through to execution from clear state
            # as we can still prolong this path
        else:
            return Result.UNSAFE, r

        return None, r

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            first_loc = path.first()
            if self._is_init(first_loc):
                r, states = self.checkInitialPath(path)
                if r is Result.UNSAFE:
                    return r, states.errors  # found a real error
                elif r is Result.SAFE:
                    continue  # this path is safe
                assert r is None

            r = self.executePath(path)

            oth = r.other
            if oth and any(map(lambda s: s.wasKilled(), oth)):
                return Result.UNKNOWN, oth

            step = self.getOptions().step
            if r.errors:
                has_err = True
                newpaths += self.extendPath(path, r,
                                            steps=step,
                                            atmost=step != 1)

        self.paths = newpaths

        if not has_err:
            return Result.SAFE, None

        return None, None

    def run(self, paths, maxk=None):
        dbg(
            f"Performing the k-ind algorithm for specified paths with maxk={maxk}",
            color="ORANGE")

        k = 1

        self.paths = paths

        if len(self.paths) == 0:
            dbg("Found no error state!", color='GREEN')
            return 0

        while True:
            dbg("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r, states = self.checkPaths()
            if r is Result.SAFE:
                dbg("All possible error paths ruled out!",
                    color="GREEN")
                dbg("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNSAFE:
                dbg("Error found.", color='RED')
                return 1
            elif r is Result.UNKNOWN:
                dbg("Hit a problem, giving up.", color='ORANGE')
                return 1
            else:
                assert r is None

            k += 1
            if maxk and maxk <= k:
                dbg(
                    "Hit the maximal number of iterations, giving up.",
                    color='ORANGE')
                return 1
