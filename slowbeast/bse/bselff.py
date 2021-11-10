from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.memorymodel import LazySymbolicMemoryModel
from slowbeast.symexe.symbolicexecution import SymbolicExecutor, SEOptions, SExecutor
from slowbeast.bse.bse import report_state
from slowbeast.bse.bself import BSELF, BSELFOptions, BSELFChecker
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.util.debugging import print_stdout, ldbgv
from .loopinfo import LoopInfo

from slowbeast.cfkind.relations import get_var_cmp_relations

class BSELFFSymbolicExecutor(SymbolicExecutor):
    def __init__(
            self, P, ohandler=None, opts=SEOptions(), executor=None, ExecutorClass=SExecutor, programstructure=None, fwdstates=None
    ):
        #opts.incremental_solving = True
        super().__init__(P, ohandler, opts, executor, ExecutorClass)
        self.programstructure = programstructure
        self._loop_headers = {loc.elem()[0] : loc for loc in self.programstructure.get_loop_headers()}
        self.forward_states = fwdstates
        self.loop_info = {}
        memorymodel = LazySymbolicMemoryModel(opts)
        self._indexecutor = PathExecutor(self.solver(), opts, memorymodel)

        self.create_set = self._indexecutor.create_states_set

    def ind_executor(self):
        return self._indexecutor

    def get_loop(self, loc):
        L = self.loop_info.get(loc)
        if L is None:
            loop = self.programstructure.get_loop(loc)
            if loop is None:
                return None

            L = LoopInfo(self, loop)
            self.loop_info[loc] = L
        return L

    def is_loop_header(self, inst):
        return inst in self._loop_headers

    def execute_path(self, path, fromInit=False, invariants=None):
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

            ldbgv("Executing (init) path: {0}", (path,), fn=print_stdout)
        else:
            executor = self.ind_executor()

            s = executor.create_clean_state()
            states = [s]

            ldbgv("Executing path: {0}", (path,), fn=print_stdout, color="orange")

        assert all(map(lambda s: not s.constraints(), states)), "The state is not clean"

        # execute the annotated error path and generate also
        # the states that can avoid the error at the end of the path
        r = executor.execute_annotated_path(states, path, invariants)
        self.stats.paths += 1

        earl = r.early
        if fromInit and earl:
            # this is an initial path, so every error is taken as real
            errs = r.errors or []
            for e in (e for e in earl if e.has_error()):
                errs.append(e)
            r.errors = errs

        return r

    def handleNewState(self, s):
        if s.is_ready() and self.is_loop_header(s.pc):
            self._annotate_cfa(s)
        super().handleNewState(s)

    def _annotate_cfa(self, state):
        print("HEADER:", state.pc)
        loc = self._loop_headers[state.pc]
        LI = self.get_loop(loc)
        for path in LI.paths():
            print(path)
            nxtstates, _ = self.executor().execute_bblocks_path(state.copy(),
                                                                path.bblocks())
            if not nxtstates:
                continue
            assert len(nxtstates) == 1
            nxtstates[0].dump()
            print(list(get_var_cmp_relations(nxtstates[0], self.create_set(nxtstates[0]))))

        assert False

        # S = self.create_set(state)
        # A, rels, states = self.forward_states.setdefault(loc, (self.create_set(), set(), []))
        cur_rels = set()
        for rel in (r for r in get_var_cmp_relations(state, A) if r not in rels):
            if rel.get_cannonical().is_concrete(): # True
                continue
            rels.add(rel)
            cur_rels.add(rel)
            print('rel', rel)
            A.add(S)
            #sts = LI.execute(pre=self.create_set(rel))
            nxt_rels = set()
            for s in (sts.ready or []):
                for r in get_var_cmp_relations(s, S):
                    if r in nxt_rels:
                        continue
                    nxt_rels.add(r)
                    print('nxt', r)

        states.append((state, rels))


class BSELFF(BSELF):
    """
    The main class for BSELFF (BSELF with forward analysis)
    """

    def __init__(self, prog, ohandler=None, opts=BSELFOptions()):
        print("BSELF^2")
        super().__init__(prog, ohandler, opts)
        self.forward_states = {}
        # self.create_set = self.ind_executor().create_states_set


    def run(self):
        se = BSELFFSymbolicExecutor(self.program, self.ohandler, self.options,
                                    programstructure=self.programstructure,
                                    fwdstates=self.forward_states)
        se.prepare()
        se_checkers = [se]

        bself_checkers = []
        for loc, A in self._get_possible_errors():
            print_stdout(f"Checking possible error: {A.expr()} @ {loc}", color="white")
            checker = BSELFChecker(
                loc,
                A,
                self.program,
                self.programstructure,
                self.options,
                invariants=self.invariants,
            )
            checker.init_checker()
            bself_checkers.append(checker)

        while True:
            for checker in se_checkers:
                checker.do_step()
                # forward SE found an error
                if checker.stats.errors > 0:
                    return Result.UNSAFE
                # forward SE searched whole program and found not error
                if not checker.states and checker.stats.killed_paths == 0:
                    return Result.SAFE

            bself_has_unknown = False
            remove_checkers = []
            for checker in bself_checkers:
                continue
                result, states = checker.do_step()
                if result is None:
                    continue
                self.stats.add(checker.stats)
                if result is Result.UNSAFE:
                    # FIXME: report the error from bsecontext
                    print_stdout(
                        f"{states.get_id()}: [assertion error]: {loc} reachable.",
                        color="redul",
                    )
                    print_stdout(str(states), color="wine")
                    print_stdout("Error found.", color="redul")
                    self.stats.errors += 1
                    return result
                if result is Result.SAFE:
                    print_stdout(
                        f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                    )
                    remove_checkers.append(checker)
                elif result is Result.UNKNOWN:
                    print_stdout(f"Checking {A} at {loc} was unsuccessful.", color="yellow")
                    bself_has_unknown = True
                    assert checker.problematic_states, "Unknown with no problematic paths?"
                    for p in checker.problematic_states:
                        report_state(self.stats, p)

            for c in remove_checkers:
                bself_checkers.remove(c)
            if not bself_checkers:
                if bself_has_unknown:
                    print_stdout("Failed deciding the result.", color="orangeul")
                    return Result.UNKNOWN

                print_stdout("No error found.", color="greenul")
                ohandler = self.ohandler
                if ohandler:
                    ohandler.testgen.generate_proof(self)
                return Result.SAFE