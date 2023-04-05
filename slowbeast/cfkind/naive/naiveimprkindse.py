from copy import copy

from slowbeast.cfkind.annotatedcfg import CFG
from slowbeast.cfkind.naive.inductionpath import InductionPath
from slowbeast.cfkind.naive.naivekindse import (
    KindSymbolicInterpreter as BasicKindSymbolicExecutor,
)
from slowbeast.cfkind.naive.naivekindse import Result, KindSeOptions
from slowbeast.symexe.executionstate import SEState
from slowbeast.symexe.interpreter import SEOptions
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from slowbeast.cfkind import KindSEOptions


class KindSymbolicExecutor(BasicKindSymbolicExecutor):
    def __init__(
        self, prog, ohandler=None, opts: KindSEOptions = KindSeOptions()
    ) -> None:
        super(KindSymbolicExecutor, self).__init__(prog, opts)

        self.cfgs = {}
        self._infeasibleSuffixes = []

    def get_cfg(self, F):
        return self.cfgs.setdefault(F, CFG(F))

    def has_infeasible_suffix(self, path) -> bool:
        for p in self._infeasibleSuffixes:
            if path.get_path().endswith(p):
                return True
        return False

    def execute_path(self, path):
        print_stdout(f"Executing path: {path}", color="ORANGE")
        ready, notready = self.ind_executor().execute_edge(
            path.get_state(), path.get_path()
        )
        return ready, notready

    def extend_induction_hypothesisPath(self, path):
        newpaths = []
        found_err = False

        for p in path.extend():
            if not p.reaches_assert():
                newpaths.append(p)
                continue

            if self.has_infeasible_suffix(p):
                # FIXME: this works only for "assert False" as it is in its own
                # block...
                dbg(f"Skipping path with infeasible suffix: {p}")
                continue

            # this path may reach an assert
            # so we must really execute it and get those
            # states that do no violate the assert
            ready, notready = self.execute_path(p)

            newpaths += [InductionPath(r) for r in ready]

            if len(notready) == 0 and len(ready) == 0:
                self._infeasibleSuffixes.append(p.get_path())

            for ns in notready:
                if ns.has_error():
                    found_err = True
                    dbg(
                        "Hit error state in induction check: {0}: {1}, {2}".format(
                            ns.get_id(), ns.pc, ns.get_error()
                        ),
                        color="PURPLE",
                    )
                if ns.is_killed():
                    print_stderr(
                        ns.status_detail(), prefix="KILLED STATE: ", color="WINE"
                    )
                    return [], Result.UNKNOWN

        return newpaths, Result.UNSAFE if found_err else Result.SAFE

    def extend_paths(self, ind):
        found_err = False
        newpaths = []
        for path in ind:
            tmp, f_err = self.extend_induction_hypothesisPath(path)
            if f_err == Result.UNKNOWN:
                return [], Result.UNKNOWN
            newpaths += tmp
            found_err |= f_err == Result.UNSAFE

        return newpaths, Result.UNSAFE if found_err else Result.SAFE

    def extend_induction_hypothesis(self) -> None:
        pass  # we do all the work in check_induction_step

    def check_induction_step(self):
        self.ind, safe = self.extend_paths(self.ind)
        return safe

    def initialize_induction(self):
        cfg = self.get_cfg(self.get_program().entry())
        ind, done = super(KindSymbolicExecutor, self).initialize_induction()
        if done:
            return [], True
        # we do the first extension here, so that we can do the rest of the
        # work in check_induction_step and do not execute the paths repeatedly
        return self.extend_paths([InductionPath(cfg, s) for s in ind])
