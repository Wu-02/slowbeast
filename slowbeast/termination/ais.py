from typing import Optional

from slowbeast.analysis.programstructure import ProgramStructure
from slowbeast.bse.bself import BSELFChecker
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.symexe.statesset import intersection
from slowbeast.termination.ais_overapproximations import overapprox_state
from slowbeast.termination.inductivesetstree import InductiveSetsTree
from slowbeast.util.debugging import print_stdout, print_stderr, dbg


class AisInference(BSELFChecker):
    """
    Infer acyclic inductive sets for one loop
    """

    def __init__(
        self,
        loc,
        program,
        programstructure: Optional[ProgramStructure],
        opts,
        invariants=None,
        indsets=None,
        max_loop_hits=None,
    ) -> None:
        super().__init__(
            loc,
            None,
            program,
            programstructure,
            opts,
            invariants,
            indsets,
            max_loop_hits,
        )

        self.loop = self.get_loop(loc)
        # tell the super() class what is the assertion that we are looking for
        S = self.get_loop_termination_condition(loc)
        self.aistree = InductiveSetsTree(S)

        # TODO: do we need this?
        self.assertion = S.as_assert_annotation()
        print_stdout(
            f"Init AIS for loop {loc} with termination condition {self.assertion}",
            color="cyan",
        )

    def get_loop_termination_condition(self, loc):
        S = self.create_set()
        for path in self.loop.get_exit_paths():
            result = self.execute_path(path)
            S.add(result.ready)
        assert not S.is_empty(), "Got no loop termination condition"
        return S

    def unwind(self, loc, errpre, maxk=None) -> int:
        raise RuntimeWarning("Do not want to do unwinding (not now)")
        return Result.UNKNOWN

    def do_step(self):
        print_stdout(
            f"[loop {self.location}] current AIS: {self.aistree.all_states.as_assume_annotation()}",
            color="blue",
        )

        overapprox_step = self.overapprox_step
        aistree = self.aistree
        for frontier_node in aistree.frontiers.copy():
            prestates = self._extend_one_step(self.loop, frontier_node.iset)
            if prestates is None:
                print_stderr(f"Got no prestates of {frontier_node.iset}")
                aistree.frontiers.remove(frontier_node)
                continue
            for state in prestates:
                dbg(f"Pre-image {self.create_set(state).as_assume_annotation()}")
                overapprox_step(aistree, frontier_node, state)

    def overapprox_step(self, aistree, frontier_node, state):
        loop = self.loop
        n = 0
        state_as_set = self.create_set(state)
        # this is a reference, so every iteration in the loop below
        # will use an updated current_ais by previous iterations
        current_ais = aistree.all_states
        X = state_as_set.copy()
        X.intersect(current_ais)
        if not X.is_empty():
            # NOT HANDLED YET
            print_stdout("Prestate overlaps with AIS", color="red")
            return None

        for overapprox in overapprox_state(
            executor=self,
            state_as_set=state_as_set,
            errset=current_ais,
            target=current_ais,
            loopinfo=loop,
        ):
            n += 1
            if overapprox is None:
                dbg("Overapproximation failed...")
                continue

            if __debug__:
                assert (
                    overapprox is None
                    or intersection(overapprox, current_ais).is_empty()
                ), f"Overapproximation overlaps with current states: {overapprox}"
            aistree.add_set(overapprox, frontier_node)
            print_stdout(
                f"[loop {self.location}] new AIS: {self.aistree.all_states.as_assume_annotation()}",
                color="blue",
            )
