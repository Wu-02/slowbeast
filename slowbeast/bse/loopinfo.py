from slowbeast.bse.bse import check_paths
from slowbeast.solvers.solver import getGlobalExprManager, IncrementalSolver
from slowbeast.symexe.annotations import execute_annotation_substitutions
from slowbeast.symexe.statesset import union


class LoopInfo:
    def __init__(self, executor, loop):
        self.loop = loop
        self.cfa = loop.cfa
        self.header = loop.header
        self.entries = loop.entries
        self.get_exit_paths = loop.get_exit_paths
        self.paths_to_header = loop.paths_to_header
        self.exits = loop.exits

        self.indexecutor = executor.ind_executor()

        self.prestate = executor.ind_executor().createCleanState()
        poststates = check_paths(executor, loop.paths()).ready
        assert poststates, "Loop has no infeasible path"
        self.poststates = poststates

    def paths(self):
        return self.loop.paths()

    def set_is_inductive(self, S):
        em = getGlobalExprManager()
        solver = IncrementalSolver()

        annot = S.as_assume_annotation()
        prestates, _ = execute_annotation_substitutions(
            self.indexecutor, [self.prestate], annot
        )
        assert len(prestates) == 1, prestates
        solver.add(annot.do_substitutions(prestates[0]))

        poststates, _ = execute_annotation_substitutions(
            self.indexecutor, self.poststates, annot
        )
        Not = em.Not
        for s in poststates:
            solver.push()
            solver.add(s.path_condition())
            expr = annot.do_substitutions(s)
            if solver.is_sat(Not(expr)) is True:
                solver.pop()
                return False
            solver.pop()

        return True

    def set_is_inductive_towards(self, S, target, allow_infeasible_only=False):
        em = getGlobalExprManager()
        solver = IncrementalSolver()

        preannot = S.as_assume_annotation()
        postannot = union(S, target).as_assume_annotation()
        prestates, _ = execute_annotation_substitutions(
            self.indexecutor, [self.prestate], preannot
        )
        poststates, _ = execute_annotation_substitutions(
            self.indexecutor, self.poststates, postannot
        )

        assert len(prestates) == 1, prestates
        solver.add(preannot.do_substitutions(prestates[0]))

        Not = em.Not
        has_feasible = False
        for s in poststates:
            solver.push()
            solver.add(s.path_condition())
            if solver.is_sat() is False:
                solver.pop()
                continue # infeasible path
            has_feasible = True
            expr = postannot.do_substitutions(s)
            if solver.is_sat(Not(expr)) is True:
                solver.pop()
                return False
            solver.pop()

        return has_feasible or allow_infeasible_only