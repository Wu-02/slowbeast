from copy import copy


class ConstraintsSet:
    __slots__ = ['constraints', '_ro']

    def __init__(self, C=[]):
        self.constraints = C
        self._ro = False

    def copy(self):
        new = copy(self)
        new._ro = True
        return new

    def __eq__(self, rhs):
        return self.constraints == rhs.constraints

    def addConstraint(self, *C):
        if self._ro:
            # shallow copy should be enough
            self.constraints = copy(self.constraints)
            self._ro = False

        for c in C:
            assert not c.isConstant(), "Adding True or False, catch these cases atm"
            self.constraints.append(c)

    def get(self):
        return self.constraints

    def __repr__(self):
        return self.constraints.__repr__()
