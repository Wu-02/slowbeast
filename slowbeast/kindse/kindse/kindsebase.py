from slowbeast.util.debugging import print_stderr, print_stdout, dbg

from slowbeast.kindse.annotatedcfg import CFG
from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.dfs import DFSVisitor, DFSEdgeType
from slowbeast.analysis.callgraph import CallGraph
from slowbeast.symexe.symbolicexecution import (
    SymbolicExecutor as SymbolicInterpreter,
)
from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions


def check_paths(executor, paths, pre=None, post=None):
    result = PathExecutionResult()
    for path in paths:
        p = path.copy()
        # the post-condition is the whole frame
        if post:
            p.add_annot_after(post.as_assert_annotation())

        if pre:
            p.add_annot_before(pre.as_assume_annotation())

        r = executor.executePath(p)
        result.merge(r)

    return result


def find_loop_headers(cfas, new_output_file=None):
    headers = set()

    def processedge(edge, dfstype):
        if dfstype == DFSEdgeType.BACK:
            headers.add(edge.target())

    for cfa in cfas.values():
        if __debug__:
            if new_output_file:
                with new_output_file(f"{cfa.fun().name()}-dfs.dot") as f:
                    DFSVisitor().dump(cfa, f)

        DFSVisitor().foreachedge(cfa.entry(), processedge)

    return headers


class ProgramStructure:
    def __init__(self, prog, new_dbg_file=None):
        self.new_dbg_file = new_dbg_file
        callgraph = CallGraph(prog)
        if __debug__:
            with new_dbg_file("callgraph-full.txt") as f:
                callgraph.dump(f)

        callgraph.pruneUnreachable(prog.entry())
        if __debug__:
            with new_dbg_file("callgraph.txt") as f:
                callgraph.dump(f)

        self.callgraph = callgraph
        cfas = CFA.from_program(prog, callgraph)
        if __debug__:
            for fun, cfa in cfas.items():
                with self.new_dbg_file(f"cfa.{fun.name()}.dot") as f:
                    cfa.dump(f)
        self.cfas = cfas
        # entry location of the whole program
        self.entry_loc = cfas[prog.entry()].entry()

        self.loop_headers = None

    def get_loop_headers(self):
        # FIXME: do it separately for each CFA
        headers = self.loop_headers
        if headers is None:
            headers = find_loop_headers(self.cfas, self.new_dbg_file)
            self.loop_headers = headers
        return headers


class KindSymbolicExecutor(SymbolicInterpreter):
    def __init__(
        self, prog, ohandler=None, opts=KindSeOptions(), programstructure=None
    ):
        super().__init__(
            P=prog, ohandler=ohandler, opts=opts, ExecutorClass=PathExecutor
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = LazySymbolicMemoryModel(opts)
        indexecutor = PathExecutor(self.solver(), opts, memorymodel)
        # add error funs and forbid defined calls...
        dbg("Forbidding calls in induction step for now with k-induction")
        indexecutor.forbidCalls()
        self._indexecutor = indexecutor

        if programstructure is None:
            self.programstructure = ProgramStructure(prog, self.new_output_file)
        else:
            self.programstructure = programstructure

        self._entry_loc = self.programstructure.entry_loc
        self.paths = []
        # as we run the executor in nested manners,
        # we want to give different outputs
        self.reportfn = print_stdout

        self.have_problematic_path = False
        # here we report error states
        self.return_states = None

    def ind_executor(self):
        return self._indexecutor

    def get_cfa(self, F):
        assert self.programstructure.cfas.get(F), f"Have no CFA for function {F.name()}"
        return self.programstructure.cfas.get(F)

    def get_return_states(self):
        """
        The states that caused killing the execution,
        i.e., error states or killed states
        """
        return self.return_states

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
            executor = self.executor()

            if not self.states:
                self.prepare()
            states = [s.copy() for s in self.states]
            assert states

            dbg(f"Executing (init) path: {path}", fn=self.reportfn)
        else:
            executor = self.ind_executor()

            s = executor.createCleanState()
            states = [s]

            dbg(f"Executing path: {path}", fn=self.reportfn)

        assert all(
            map(lambda s: not s.getConstraints(), states)
        ), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.execute_annotated_path(states, path)
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
        return loc is self._entry_loc

    def extend_to_caller(self, path, states):
        self.have_problematic_path = True
        print_stdout("Killing a path that goes to caller")
        # start = path.first()
        # cgnode = self.programstructure.callgraph.getNode(start.bblock().fun())
        # for callerfun, callsite in cgnode.getCallers():
        #    print('caller', callerfun.fun())
        #    print('cs', callsite)
        #    callsite.bblock()
        return []

    def extend_path(self, path, states, steps=-1, atmost=False, stoppoints=[]):
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
        locs = path.edges()[:]
        locs.reverse()  # reverse the list so that we can do append
        worklist = [locs]
        while worklist:
            num += 1
            newworklist = []

            for p in worklist:
                front = p[-1]  # the list is reversed, so the front is at the end
                preds = front.source().predecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    if len(path) == len(p) and states:
                        # we did not extend the path at all, so this
                        # is a path that ends in the entry block and
                        # we already processed it...
                        dbg("Extending a path to the caller")
                        np = self.extend_to_caller(path, states)
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

                    assert all(map(lambda x: isinstance(x, CFA.Location), stoppoints))
                    if pred in stoppoints:
                        newpath.reverse()
                        newpaths.append(path.copyandsetpath(newpath))
                    elif steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    elif steps == -1 and len(pred.source().successors()) > 1:
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
                fn(
                    "state {0}: {1}, {2}".format(n.get_id(), n.pc, n.getError()),
                    color="RED",
                )
            self.stats.errors += 1
            return Result.UNSAFE
        elif n.wasKilled():
            if fn:
                fn(n.getStatusDetail(), prefix="KILLED STATE: ", color="WINE")
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
            killed = any(True for s in r.early if s.wasKilled()) if r.early else None
            if killed:
                return Result.UNKNOWN, r
            killed = any(True for s in r.other if s.wasKilled()) if r.other else None
            if killed:
                return Result.UNKNOWN, r
            if len(self._entry_loc.predecessors()) == 0:
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
                newpaths += self.extend_path(path, r, steps=step, atmost=step != 1)

        self.paths = newpaths

        if not has_err:
            return Result.SAFE, None

        return None, None

    def run(self, paths, maxk=None):
        dbg(
            f"Performing the k-ind algorithm for specified paths with maxk={maxk}",
            color="ORANGE",
        )

        k = 1

        self.paths = paths

        if len(self.paths) == 0:
            dbg("Found no error state!", color="GREEN")
            return 0

        while True:
            dbg("-- starting iteration {0} --".format(k))
            dbg("Got {0} paths in queue".format(len(self.paths)))

            r, states = self.checkPaths()
            if r is Result.SAFE:
                dbg("All possible error paths ruled out!", color="GREEN")
                dbg("Induction step succeeded!", color="GREEN")
                return r
            elif r is Result.UNSAFE:
                self.return_states = states
                dbg("Error found.", color="RED")
                return r
            elif r is Result.UNKNOWN:
                self.return_states = states
                dbg("Hit a problem, giving up.", color="ORANGE")
                return r
            else:
                assert r is None

            k += 1
            if maxk and maxk <= k:
                dbg("Hit the maximal number of iterations, giving up.", color="ORANGE")
                return Result.UNKNOWN
