from slowbeast.util.debugging import print_stderr, print_stdout, dbg

from slowbeast.kindse.annotatedcfg import CFG, CFGPath
from slowbeast.kindse.naive.naivekindse import KindSymbolicExecutor as BasicKindSymbolicExecutor
from slowbeast.kindse.naive.naivekindse import Result, KindSeOptions
from slowbeast.kindse.naive.inductionpath import InductionPath

from copy import copy


class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
            self,
            prog,
            testgen=None,
            opts=KindSeOptions()):
        super(
            KindSymbolicExecutor, self).__init__(prog, opts)

        self.cfgs = {}
        self.paths = []

    def getCFG(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def executePath(self, path, fromInit=False):
        if fromInit:
            if not self.states:
                self.prepare()
            states = self.states
            assert states
            print_stdout(
                "Executing path from init: {0}".format(path),
                color="ORANGE")
            # we must execute without lazy memory
            executor = self.getExecutor()
        else:
            s = self.getIndExecutor().createState()
            s.pushCall(None, self.getProgram().getEntry())
            states = [s]
            executor = self.getIndExecutor()

            print_stdout("Executing path: {0}".format(path), color="ORANGE")

        assert states

        ready, notready = executor.executePath(states, path)
        self.stats.paths += 1
        return ready, notready

   # def extendPath(self, path, atmost=False):
   #    front = path.first()

   #    preds = front.getPredecessors()
   #    # FIXME: do not do this prepend, we always construct a new list....
   #    # rather do append and then execute in reverse order (do a reverse
   #    # iterator)
   #    newpaths = [CFGPath([p] + path.getLocations()) for p in preds]

   #    if atmost and len(preds) == 0:
   #        assert len(newpaths) == 0
   #        newpaths.append(path)

   #    return newpaths

    def extendPath(self, path, steps=0, atmost=False):
        """
        Take a path and extend it by prepending one or more
        predecessors.

        \param steps     Number of predecessors to prepend.
                         Values less or equal to 0 have a special
                         meaning:
                           0 -> prepend until a join is find
        \param atmost    if set to True, we allow to extend
                         less than the specified number of steps
                         if there are no predecessors.
                         If set to False, the path is dropped
                         if it cannot be extended (there are
                         not enough predecessors)
        """

        num = 0
        newpaths = []
        worklist = [path]
        while worklist:
            num += 1
            newworklist = []

            for p in worklist:
                front = p.first()
                preds = front.getPredecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    newpaths.append(p)
                    continue

                for pred in preds:
                    # FIXME: do not do this prepend, we always construct a new list....
                    # rather do append and then execute in reverse order (do a reverse
                    # iterator?)
                    newpath = CFGPath([pred] + p.getLocations())

                    if steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    else:  # we're done with this path
                        newpaths.append(newpath)

            worklist = newworklist

        return newpaths

    def _is_init(self, loc):
        return loc.getBBlock() is self.getProgram().getEntry().getBBlock(0)

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

    def checkPaths(self):
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            # FIXME: use also the ready paths to constraint the state space
            # in the future

            first_loc = path.first()
            if self._is_init(first_loc):
                # try executing the path from initial states
                _, notready = self.executePath(path, fromInit=True)
                if not notready:
                    if len(first_loc.getPredecessors()) == 0:
                        # this path is safe and we do not need to extend it
                        continue
                    # else just fall-through to execution from clear state
                    # as we can still prolong this path
                else:
                    for n in notready:
                        # we found a real error
                        if n.hasError():
                            return self.report(n)
                        if n.wasKilled():
                            return self.report(n)

            _, notready = self.executePath(path)

            step = self.getOptions().step
            for n in notready:
                if n.hasError():
                    has_err = True
                    newpaths += self.extendPath(path, steps=step)
                    break
                if n.wasKilled():
                    return self.report(n)

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

    def initializePaths(self, k=1):
        paths = []
        cfg = self.getCFG(self.getProgram().getEntry())
        nodes = cfg.getNodes()
        paths = [CFGPath([n]) for n in nodes if n.hasAssert()]
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