from copy import copy


class ConstraintsSet:
    __slots__ = ["constraints"]

    def __init__(self, C=None):
        self.constraints = []
        if C:
            self.addConstraint(*C)

    def copy(self):
        return ConstraintsSet(self.constraints.copy())

    def __eq__(self, rhs):
        return self.constraints == rhs.constraints

    def addConstraint(self, *C):
        constr = self.constraints
        for c in C:
            #assert not c.isConstant(), "Adding True or False, catch these cases atm"
            if c.isConstant():
                if c.getValue() is False:
                    self.constraints = [c]
                    break
                # we can ignore True...
            if c.isAnd():
                constr.extend(c.children())
            else:
                constr.append(c)

    def asFormula(self, EM):
        return EM.conjunction(*self.constraints)

    def get(self):
        return self.constraints

    def __repr__(self):
        return self.constraints.__repr__()
