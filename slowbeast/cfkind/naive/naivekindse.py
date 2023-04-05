from slowbeast.cfkind import KindSEOptions
from slowbeast.symexe.iexecutor import IExecutor, IExecutor as SExecutor
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.symexe.interpreter import SymbolicInterpreter
from slowbeast.util.debugging import print_stderr, print_stdout, dbg
from typing import Optional


class Result:
    UNKNOWN = 0
    SAFE = 1
    UNSAFE = 2


class KindSymbolicInterpreter(SymbolicInterpreter):
    def __init__(
        self, prog, ohandler=None, opts: KindSEOptions = KindSEOptions()
    ) -> None:
        super(KindSymbolicInterpreter, self).__init__(
            P=prog, ohandler=ohandler, opts=opts
        )

        # the executor for induction checks -- we need lazy memory access
        memorymodel = LazySymbolicMemoryModel(opts)
        self.indexecutor = SExecutor(self.solver(), opts, memorymodel)
        dbg("Forbidding calls in induction step for now with k-induction")
        self.indexecutor.forbid_calls()

    def ind_executor(self) -> IExecutor:
        return self.indexecutor

    def extend_base_step(self) -> Optional[int]:
        states = self.executor().execute_till_branch(self.base)
        self.base = []
        for ns in states:
            if ns.has_error():
                print_stderr(
                    f"{ns.get_id()}: {ns.pc}, {ns.get_error()}",
                    color="RED",
                )
                self.stats.errors += 1
                self.stats.paths += 1
                return Result.UNSAFE
            elif ns.is_ready():
                self.base.append(ns)
            elif ns.is_terminated():
                print_stderr(ns.get_error(), color="BROWN")
                self.stats.paths += 1
                self.stats.terminated_paths += 1
            elif ns.is_killed():
                self.stats.paths += 1
                self.stats.killed_paths += 1
                print_stderr(ns.status_detail(), prefix="KILLED STATE: ", color="WINE")
                return Result.UNKNOWN
            else:
                assert ns.exited()
                self.stats.paths += 1
                self.stats.exited_paths += 1

        if not self.base:
            # no ready states -> we searched all the paths
            return Result.SAFE

        return None

    def extend_induction_hypothesis(self) -> int:
        states = self.indexecutor.execute_till_branch(self.ind)

        self.ind = []
        found_err = False
        for ns in states:
            if ns.has_error():
                found_err = True
                dbg(
                    "Hit error state while building IS assumptions: {0}: {1}, {2}".format(
                        ns.get_id(), ns.pc, ns.get_error()
                    ),
                    color="PURPLE",
                )
            elif ns.is_ready():
                self.ind.append(ns)
            elif ns.is_terminated():
                print_stderr(ns.get_error(), color="BROWN")
            elif ns.is_killed():
                print_stderr(ns.status_detail(), prefix="KILLED STATE: ", color="WINE")
                return Result.UNKNOWN
            else:
                assert ns.exited()

        return Result.UNSAFE if found_err else Result.SAFE

    def check_induction_step(self) -> int:
        frontier = [s.copy() for s in self.ind]
        states = self.indexecutor.execute_till_branch(frontier)

        has_error = False
        for ns in states:
            if ns.has_error():
                has_error = True
                dbg(
                    "Induction check hit error state: {0}: {1}, {2}".format(
                        ns.get_id(), ns.pc, ns.get_error()
                    ),
                    color="PURPLE",
                )
                break
            elif ns.is_killed():
                print_stderr(ns.status_detail(), prefix="KILLED STATE: ", color="WINE")
                return Result.UNKNOWN

        return Result.UNSAFE if has_error else Result.SAFE

    def initialize_induction(self):
        ind = []
        bblocks = self.get_program().entry().bblocks()
        executor = self.indexecutor
        entry = self.get_program().entry()
        append = ind.append
        for b in bblocks:
            s = executor.create_state()
            s.push_call(None, entry)
            s.pc = b.first()
            append(s)
        return ind, False

    def run(self) -> int:
        self.prepare()

        dbg("Performing the k-ind algorithm only for the main function", color="ORANGE")

        k = 1
        self.base = self.states  # start from the initial states
        self.ind, safe = self.initialize_induction()

        if safe:
            print_stdout("Found no error state!", color="GREEN")
            return 0

        while True:
            print_stdout(f"-- starting iteration {k} --")

            dbg("Extending base".format(k), color="BLUE")
            r = self.extend_base_step()
            if r == Result.UNSAFE:
                print_stdout("Error found.", color="RED")
                return 1
            elif r is Result.SAFE:
                print_stdout("We searched the whole program!", color="GREEN")
                return 0
            elif r is Result.UNKNOWN:
                print_stdout("Hit a problem, giving up.", color="ORANGE")
                return 1

            dbg("Extending induction step".format(k), color="BLUE")
            r = self.extend_induction_hypothesis()
            if r == Result.SAFE:
                print_stdout(
                    "Did not hit any possible error while building "
                    "induction step!".format(k),
                    color="GREEN",
                )
                return 0
            elif r is Result.UNKNOWN:
                print_stdout("Hit a problem, giving up.", color="ORANGE")
                return 1

            dbg("Checking induction step".format(k), color="BLUE")
            r = self.check_induction_step()
            if r == Result.SAFE:
                print_stdout("Induction step succeeded!", color="GREEN")
                return 0
            elif r is Result.UNKNOWN:
                print_stdout("Hit a problem, giving up.", color="ORANGE")
                return 1

            k += 1
