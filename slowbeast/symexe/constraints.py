from copy import copy


class ConstraintsSet:
    __slots__ = ['constraints', '_ro']

    def __init__(self, C=None):
        self.constraints = C or []

    def copy(self):
        return ConstraintsSet(self.constraints[:])

    def __eq__(self, rhs):
        return self.constraints == rhs.constraints

    def addConstraint(self, *C):
        for c in C:
            assert not c.isConstant(), "Adding True or False, catch these cases atm"
            self.constraints.append(c)

    def asFormula(self, EM):
        return EM.conjunction(*self.constraints)

    def get(self):
        return self.constraints

    def __repr__(self):
        return self.constraints.__repr__()
