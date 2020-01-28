from pysmt.shortcuts import Or, And, Not, Symbol, BV
from pysmt.typing import BVType

from .. ir.types import Type
from .. ir.value import Value
from .. domains.concrete import ConcreteDomain

class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """
    def __init__(self, e, t):
        Value.__init__(self, t.getBitWidth(), isptr=False)
        self._expr = e

    def asValue(self):
        return str(self)

    def __str__(self):
        return "<{0}:{1}>".format(self._expr, self.getType())

class ExprManager:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    def __init__(self):
        self._names = {}

    def Var(self, name, bw = 64):
        assert isinstance(name, str)
        s = self._names.get(name)
        if s:
            assert s.getType() == Type(bw), "Creating the same value with different type"
        else:
            s = Expr(Symbol(name, BVType(bw)), Type(bw))
            self._names[name] = s
        assert s
        return s

    def freshValue(self, name, bw = 64):
        assert isinstance(name, str)
        s = self._names.get(name)
        while s:
            cnt = 1
            name = "{0}_{1}".format(name, cnt)
            s = self._names.get(name)

        s = Expr(Symbol(name, BVType(bw)), Type(bw))
        self._names[name] = s
        return s

    def lift(self, v):
        assert isinstance(v, Value)
        if isinstance(v, Expr):
            return v

        if v.isConstant():
            # FIXME: is 64 right?
            return Expr(BV(v.getValue(), v.getType().getBitWidth()), v.getType())

    def Int1(self, name):
        return self.var(name, 1)

    def Int8(self, name):
        return self.var(name, 8)

    def Int16(self, name):
        return self.var(name, 16)

    def Int32(self, name):
        return self.var(name, 32)

    def Int64(self, name):
        return self.var(name, 64)

    def And(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.And(a, b)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(And(a._expr, b._expr), Type(1))

    def Or(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Or(a, b)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(Or(a._expr, b._expr), Type(1))

    def Not(self, a):
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Not(a)
        a = self.lift(a)
        assert isinstance(a, Expr)
        return Expr(Not(a._expr), Type(1))

    ##
    # Relational operators

    def Le(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Le(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr <= b._expr, Type(1))

    def Lt(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Lt(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr < b._expr, Type(1))

    def Ge(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ge(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr >= b._expr, Type(1))

    def Gt(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Gt(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr > b._expr, Type(1))

    def Eq(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Eq(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr == b._expr, Type(1))

    def Ne(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ne(a)
        a = self.lift(a)
        b = self.lift(b)
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        return Expr(a._expr != b._expr, Type(1))

