from slowbeast.util.debugging import print_stderr, print_stdout, dbg

from slowbeast.kindse.annotatedcfg import CFG
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions

from slowbeast.ir.instruction import Cmp


class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions()):
        super(
            KindSymbolicExecutor,
            self).__init__(
            prog=prog,
            testgen=testgen,
            opts=opts)

        self.cfgs = {F : CFG(F) for F in prog.getFunctions() if not F.isUndefined()}
        self.paths = []

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
            if not self.states:
                self.prepare()
            states = self.states
            assert states
            print_stdout(
                f"Executing init prefix+step: {path}", color="ORANGE")
            # we must execute without lazy memory
            executor = self.getExecutor()
        else:
            s = self.getIndExecutor().createState()
            s.pushCall(None, self.getProgram().getEntry())
            states = [s]
            executor = self.getIndExecutor()

            print_stdout(f"Executing prefix+step: {path}", color="ORANGE")

        assert states

        # execute the prefix of the path and do one more step
        safe, unsafe, earlyterm = executor.executeAnnotatedStepWithPrefix(
            states, path)
        self.stats.paths += 1

        if fromInit:
            # this is an initial path, so every error is taken as real
            unsafe += earlyterm

        return safe, unsafe

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

    def extendPath(self, path, steps=-1, atmost=False, stoppoints=[]):
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

        dbg(f"Extending {path}")
        num = 0
        newpaths = []
        locs = path.getLocations()[:]
        locs.reverse() # reverse the list so that we can do append
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

    def checkInitialPath(self, path):
        """
        Execute a path from initial states
        \requires an initial path
        """

        safe, unsafe = self.executePath(path, fromInit=True)
        if not unsafe:
            if len(path.first().getPredecessors()) == 0:
                # this path is safe and we do not need to extend it
                return Result.SAFE
            # else just fall-through to execution from clear state
            # as we can still prolong this path
        else:
            for n in unsafe:
                # we found a real error or hit another problem
                if n.hasError() or n.wasKilled():
                    return Result.UNSAFE
                else:
                    assert False, "Unhandled unsafe state"
        return None

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            first_loc = path.first()
            if self._is_init(first_loc):
                r = self.checkInitialPath(path)
                if r is Result.UNSAFE:
                    return r  # found a real error
                elif r is Result.SAFE:
                    continue  # this path is safe
                assert r is None

            safe, unsafe = self.executePath(path)

            step = self.getOptions().step
            for n in unsafe:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path,
                                                steps=step,
                                                atmost=step != 1)
                    break
                elif n.wasKilled():
                    return Result.UNKNOWN
                elif n.isTerminated():
                    continue
                else:
                    assert False, "Unhandled Unsafe state"

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

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

            r = self.checkPaths()
            if r is Result.SAFE:
                dbg(
                    "All possible error paths ruled out!",
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
