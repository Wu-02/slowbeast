from slowbeast.solvers.solver import IncrementalSolver


class ConstraintsSet:
    __slots__ = "_constraints"

    def __init__(self, C=None):
        self._constraints = []
        if C:
            self.add(*C)

    def copy(self):
        n = ConstraintsSet()
        n._constraints = self._constraints.copy()
        return n

    def __eq__(self, rhs):
        return self._constraints == rhs._constraints

    def add(self, *C):
        constr = self._constraints
        for c in C:
            # assert not c.is_concrete(), "Adding True or False, catch these cases atm"
            if c.is_concrete():
                if c.value() is False:
                    self._constraints = [c]
                    break
                # we can ignore True...
            elif c.isAnd():
                constr.extend(c.children())
            else:
                constr.append(c)

    def as_formula(self, EM):
        return EM.conjunction(*self._constraints)

    def get(self):
        return self._constraints

    def __repr__(self):
        return self._constraints.__repr__()


class IncrementalConstraintsSet(ConstraintsSet):
    __slots__ = "_solver", "_solver_ro"

    def __init__(self, C=None):
        self._solver = IncrementalSolver()
        super().__init__(C)

    def solver(self):
        return self._solver

    def copy(self):
        n = IncrementalConstraintsSet()
        self._constraints = self._constraints.copy()
        self._solver = self._solver.copy()
        return n

    def add(self, *C):
        self._solver.add(*C)
        super().add(*C)
