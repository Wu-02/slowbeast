from .. ir.types import Type
from .. ir.value import Value
from .. domains.concrete import ConcreteDomain
from .. domains.symbolic import *


def is_symbolic(v):
    return SymbolicDomain.belongto(v)


def is_concrete(v):
    assert not ConcreteDomain.belongto(v) or not is_symbolic(v)
    return ConcreteDomain.belongto(v)


class ExprManager:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    def __init__(self):
        self._names = {}

    def Constant(self, c, bw):
        return ConcreteDomain.Constant(c, bw)

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
        origname = name
        cnt = 1
        s = self._names.get(name)
        while s:
            cnt += 1
            name = "{0}_{1}".format(origname, cnt)
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

    def Le(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Le(a, b, unsigned)
        return SymbolicDomain.Le(self.lift(a), self.lift(b), unsigned)

    def Lt(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Lt(a, b, unsigned)
        return SymbolicDomain.Lt(self.lift(a), self.lift(b), unsigned)

    def Ge(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ge(a, b, unsigned)
        return SymbolicDomain.Ge(self.lift(a), self.lift(b), unsigned)

    def Gt(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Gt(a, b, unsigned)
        return SymbolicDomain.Gt(self.lift(a), self.lift(b), unsigned)

    def Eq(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Eq(a, b, unsigned)
        return SymbolicDomain.Eq(self.lift(a), self.lift(b), unsigned)

    def Ne(self, a, b, unsigned = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ne(a, b, unsigned)
        return SymbolicDomain.Ne(self.lift(a), self.lift(b), unsigned)

    ##
    # Artihmetic operations
    def Add(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Add(a, b)
        return SymbolicDomain.Add(self.lift(a), self.lift(b))

    def Sub(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Sub(a)
        return SymbolicDomain.Sub(self.lift(a), self.lift(b))

    def Mul(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Mul(a)
        return SymbolicDomain.Mul(self.lift(a), self.lift(b))

    def Div(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Div(a)
        return SymbolicDomain.Div(self.lift(a), self.lift(b))
