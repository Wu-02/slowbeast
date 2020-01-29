from .. ir.types import Type
from .. ir.value import Value
from .. domains.concrete import ConcreteDomain
from .. domains.symbolic import *


class ExprManager:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    def __init__(self):
        self._names = {}

    def Var(self, name, bw=64):
        assert isinstance(name, str)
        s = self._names.get(name)
        if s:
            assert s.getType() == Type(bw), "Creating the same value with different type"
        else:
            s = SymbolicDomain.Var(name, bw)
            self._names[name] = s
        assert s, "No var was created"
        return s

    def freshValue(self, name, bw=64):
        assert isinstance(name, str)
        s = self._names.get(name)
        while s:
            cnt = 1
            name = "{0}_{1}".format(name, cnt)
            s = self._names.get(name)

        s = SymbolicDomain.Var(name, bw)
        self._names[name] = s
        return s

    def Int1(self, name):
        return self.Var(name, 1)

    def Int8(self, name):
        return self.Var(name, 8)

    def Int16(self, name):
        return self.Var(name, 16)

    def Int32(self, name):
        return self.Var(name, 32)

    def Int64(self, name):
        return self.Var(name, 64)

    def lift(self, v):
        return SymbolicDomain.lift(v)

    def getTrue(self):
        return SymbolicDomain.getTrue()

    def getFalse(self):
        return SymbolicDomain.getFalse()

    def And(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.And(a, b)
        return SymbolicDomain.And(self.lift(a), self.lift(b))

    def Or(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Or(a, b)
        return SymbolicDomain.Or(self.lift(a), self.lift(b))

    def Not(self, a):
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Not(a)
        return SymbolicDomain.Not(self.lift(a))

    ##
    # Relational operators

    def Le(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Le(a)
        return SymbolicDomain.Le(self.lift(a), self.lift(b))

    def Lt(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Lt(a)
        return SymbolicDomain.Lt(self.lift(a), self.lift(b))

    def Ge(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ge(a)
        return SymbolicDomain.Ge(self.lift(a), self.lift(b))

    def Gt(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Gt(a)
        return SymbolicDomain.Gt(self.lift(a), self.lift(b))

    def Eq(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Eq(a)
        return SymbolicDomain.Eq(self.lift(a), self.lift(b))

    def Ne(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ne(a)
        return SymbolicDomain.Ne(self.lift(a), self.lift(b))
