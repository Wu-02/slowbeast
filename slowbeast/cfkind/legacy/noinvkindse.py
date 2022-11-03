from copy import copy

from slowbeast.cfkind import KindSEOptions
from slowbeast.cfkind.annotatedcfg import CFG, CFGPath
from slowbeast.cfkind.naive.inductionpath import InductionPath
from slowbeast.cfkind.naive.naivekindse import (
    KindSymbolicInterpreter as BasicKindSymbolicExecutor,
)
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from typing import List, Optional


class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
        self, prog, ohandler=None, opts: KindSEOptions = KindSEOptions()
    ) -> None:
        super(KindSymbolicExecutor, self).__init__(prog, opts)

        self.cfgs = {}
        self.paths = []

    def get_cfg(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def execute_path(self, path, from_init: bool = False):
        if from_init:
            if not self.states:
                self.prepare()
            states = self.states
            assert states
            print_stdout(f"Executing path from init: {path}", color="ORANGE")
            # we must execute without lazy memory
            executor = self.executor()
        else:
            s = self.ind_executor().create_state()
            s.push_call(None, self.get_program().entry())
            states = [s]
            executor = self.ind_executor()

            print_stdout(f"Executing path: {path}", color="ORANGE")

        assert states

        ready, notready = executor.execute_path(states, path)
        self.stats.paths += 1
        return ready, notready

    # def extend_path(self, path, atmost=False):
    #    front = path.first()

    #    preds = front.predecessors()
    #    # FIXME: do not do this prepend, we always construct a new list....
    #    # rather do append and then execute in reverse order (do a reverse
    #    # iterator)
    #    newpaths = [CFGPath([p] + path.locations()) for p in preds]

    #    if atmost and len(preds) == 0:
    #        assert len(newpaths) == 0
    #        newpaths.append(path)

    #    return newpaths

    def extend_path(self, path, steps: int = 0, atmost: bool = False):
        """
        Take a path and extend it by prepending one or more
        predecessors.

        \\param steps     Number of predecessors to prepend.
                         Values less or equal to 0 have a special
                         meaning:
                           0 -> prepend until a join is find
        \\param atmost    if set to True, we allow to extend
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
                preds = front.predecessors()
                predsnum = len(preds)

                # no predecessors, we're done with this path
                if atmost and predsnum == 0:
                    newpaths.append(p)
                    continue

                for pred in preds:
                    # FIXME: do not do this prepend, we always construct a new list....
                    # rather do append and then execute in reverse order (do a reverse
                    # iterator?)
                    newpath = CFGPath([pred] + p.locations())

                    if steps > 0 and num != steps:
                        newworklist.append(newpath)
                    elif steps == 0 and predsnum <= 1:
                        newworklist.append(newpath)
                    else:  # we're done with this path
                        newpaths.append(newpath)

            worklist = newworklist

        return newpaths

    def _is_init(self, loc) -> bool:
        return loc.bblock() is self.get_program().entry().bblock(0)

    def report(self, n) -> Optional[int]:
        if n.has_error():
            print_stderr("Error found.", color="red")
            print_stderr(f"{n.get_id()}: {n.pc}, {n.get_error()}", color="RED")
            self.stats.errors += 1
            return Result.UNSAFE
        elif n.was_killed():
            print_stderr(n.status_detail(), prefix="KILLED STATE: ", color="WINE")
            self.stats.killed_paths += 1
            return Result.UNKNOWN

        return None

    def check_paths(self) -> Optional[int]:
        newpaths = []
        has_err = False

        paths = self.paths
        for path in paths:
            # FIXME: use also the ready paths to constraint the state space
            # in the future

            first_loc = path.first()
            if self._is_init(first_loc):
                # try executing the path from initial states
                _, notready = self.execute_path(path, from_init=True)
                if not notready:
                    if len(first_loc.predecessors()) == 0:
                        # this path is safe and we do not need to extend it
                        continue
                    # else just fall-through to execution from clear state
                    # as we can still prolong this path
                else:
                    for n in notready:
                        # we found a real error
                        if n.has_error():
                            return self.report(n)
                        if n.was_killed():
                            return self.report(n)

            _, notready = self.execute_path(path)

            step = self.get_options().step
            for n in notready:
                if n.has_error():
                    has_err = True
                    newpaths += self.extend_path(path, steps=step)
                    break
                if n.was_killed():
                    return self.report(n)

        self.paths = newpaths

        if not has_err:
            return Result.SAFE

        return None

    def initialize_paths(self, k: int = 1) -> List[CFGPath]:
        paths = []
        cfg = self.get_cfg(self.get_program().entry())
        nodes = cfg.get_nodes()
        paths = [CFGPath([n]) for n in nodes if n.has_assert()]
        step = self.get_options().step
        while k > 0:
            paths = [
                np for p in paths for np in self.extend_path(p, steps=step, atmost=True)
            ]
            k -= 1
        return paths

    def run(self) -> int:
        dbg("Performing the k-ind algorithm only for the main function", color="ORANGE")

        k = 1

        self.paths = self.initialize_paths()

        if len(self.paths) == 0:
            print_stdout("Found no error state!", color="GREEN")
            return 0

        while True:
            print_stdout(f"-- starting iteration {k} --")
            dbg(f"Got {len(self.paths)} paths in queue")

            r = self.check_paths()
            if r is Result.SAFE:
                print_stdout("All possible error paths ruled out!", color="GREEN")
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNSAFE:
                dbg("Error found.", color="RED")
                return 1
            elif r is Result.UNKNOWN:
                print_stdout("Hit a problem, giving up.", color="ORANGE")
                return 1
            else:
                assert r is None

            k += 1
