from pysmt.shortcuts import Or, And, Not, Symbol
from pysmt.typing import BVType

from .. ir.types import Type
from .. ir.value import Value

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
        assert isinstance(a, Expr)
        assert isinstance(b, Expr)
        #assert a.getType() == Bool
        return Expr(And(a, b), Type(1))

    def Not(self, a):
        assert isinstance(a, Expr)
        return Expr(Not(a), Type(1))

    def Or(self, a, b):
        assert isinstance(a, Expr)
        return Expr(Or(a, b), Type(1))
