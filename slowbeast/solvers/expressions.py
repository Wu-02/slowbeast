from .. ir.types import Type
from .. ir.value import Value
from .. domains.concrete import ConcreteDomain
from .. domains.symbolic import *

optimize_exprs = True


def is_symbolic(v):
    return SymbolicDomain.belongto(v)


def is_concrete(v):
    assert not ConcreteDomain.belongto(v) or not is_symbolic(v)
    return ConcreteDomain.belongto(v)


class ExprOptIntf:
    """
    Expressions optimizer interface
    """
    def optimize(expr, *assumptions):
        """ Optimize the expression given the assumptions """
        return expr


class SymbolicExprOpt(ExprOptIntf):
    def optimize(expr, *assumptions):
        optexpr = SymbolicDomain.simplify(expr, *assumptions)
        # lower the symbolic expression into a concrete value
        # if possible
        const = SymbolicDomain.pythonConstant(optexpr)
        if const is not None:
            return Constant(const, optexpr.getType())
        return optexpr


if optimize_exprs:
    opt = SymbolicExprOpt.optimize
else:
    def opt(x): return x


class ExprManager:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    __slots__ = ['_names']

    def __init__(self):
        self._names = {}

    def Constant(self, c, bw):
        return ConcreteDomain.Constant(c, bw)

    def Var(self, name, bw=64):
        assert isinstance(name, str)
        names = self._names
        s = names.get(name)
        if s:
            assert s.getType() == Type(
                bw), f"Creating the same value with different type: {s.getType()} != {Type(bw)}"
        else:
            s = SymbolicDomain.Var(name, bw)
            names[name] = s
        assert s, "No var was created"
        return s

    def subexpressions(self, expr):
        if expr.isConstant():
            yield expr
        return SymbolicDomain.subexpressions(expr)

    def simplify(self, expr):
        if expr.isConstant():
            return expr
        return SymbolicExprOpt.optimize(expr)

    def freshValue(self, name, bw=64):
        assert isinstance(name, str)
        names = self._names
        origname = name
        cnt = 1
        s = names.get(name)
        while s:
            cnt += 1
            # FIXME: this is too inefficient
            # (profiling shows that this is one of the
            # bottle necks if we do not take care of
            # the uniquenes of the name on the top-level)
            name = "{0}_{1}".format(origname, cnt)
            s = names.get(name)

        s = SymbolicDomain.Var(name, bw)
        names[name] = s
        return s

    def substitute(self, expr, *vals):
        if ConcreteDomain.belongto(expr):
            return expr
        lift = self.lift
        return SymbolicDomain.substitute(
            expr, *((lift(a), lift(b)) for (a, b) in vals))

    def equals(self, e1, e2):
        """
        Values are syntactically equal
        """
        if ConcreteDomain.belongto(e1, e2):
            return e1 == e2
        lift = self.lift
        return lift(e1) == lift(e2)

    def dropValue(self, name):
        self._names.pop(name)

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

    def conjunction(self, *args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments
        """
        assert all(map(lambda a: a.isBool(), args))
        if len(args) == 0:
            return ConcreteDomain.getTrue()
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.conjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.conjunction(*map(lift, args)))

    def disjunction(self, *args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments.
        """
        assert all(map(lambda a: a.isBool(), args))
        if len(args) == 0:
            return ConcreteDomain.getFalse()
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.disjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.disjunction(*map(lift, args)))

    def And(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.And(a, b)
        return opt(SymbolicDomain.And(self.lift(a), self.lift(b)))

    def Or(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Or(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Or(lift(a), lift(b)))

    def Xor(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Xor(a, b)
        return opt(SymbolicDomain.Xor(self.lift(a), self.lift(b)))

    def Not(self, a):
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Not(a)
        return opt(SymbolicDomain.Not(self.lift(a)))

    def ZExt(self, a, b):
        assert ConcreteDomain.belongto(b), "Invalid zext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.ZExt(a, b)
        return opt(SymbolicDomain.ZExt(a, b))

    def SExt(self, a, b):
        assert ConcreteDomain.belongto(b), "Invalid sext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.SExt(a, b)
        return opt(SymbolicDomain.SExt(a, b))

    def Extract(self, a, start, end):
        assert ConcreteDomain.belongto(start, end), "Invalid sext argument"
        if ConcreteDomain.belongto(a):
            return ConcreteDomain.Extract(a, start, end)
        return opt(SymbolicDomain.Extract(a, start, end))

    def Shl(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Shl(a, b)
        return opt(SymbolicDomain.Shl(self.lift(a), self.lift(b)))

    def AShr(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.AShr(a, b)
        return opt(SymbolicDomain.AShr(self.lift(a), self.lift(b)))

    def LShr(self, a, b):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.LShr(a, b)
        return opt(SymbolicDomain.LShr(self.lift(a), self.lift(b)))

    ##
    # Relational operators

    def Le(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Le(a, b, unsigned)
        return opt(SymbolicDomain.Le(self.lift(a), self.lift(b), unsigned))

    def Lt(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Lt(a, b, unsigned)
        return opt(SymbolicDomain.Lt(self.lift(a), self.lift(b), unsigned))

    def Ge(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ge(a, b, unsigned)
        return opt(SymbolicDomain.Ge(self.lift(a), self.lift(b), unsigned))

    def Gt(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Gt(a, b, unsigned)
        return opt(SymbolicDomain.Gt(self.lift(a), self.lift(b), unsigned))

    def Eq(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Eq(a, b, unsigned)
        return opt(SymbolicDomain.Eq(self.lift(a), self.lift(b), unsigned))

    def Ne(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Ne(a, b, unsigned)
        return opt(SymbolicDomain.Ne(self.lift(a), self.lift(b), unsigned))

    ##
    # Artihmetic operations
    def Add(self, a, b):
        if ConcreteDomain.belongto(a):
            if a.getValue() == 0:
                return b
            if ConcreteDomain.belongto(b):
                if b.getValue() == 0:
                    return a
                return ConcreteDomain.Add(a, b)
        return opt(SymbolicDomain.Add(self.lift(a), self.lift(b)))

    def Sub(self, a, b):
        if ConcreteDomain.belongto(b):
            if b.getValue() == 0:
                return a
            if ConcreteDomain.belongto(a):
                return ConcreteDomain.Sub(a, b)
        return opt(SymbolicDomain.Sub(self.lift(a), self.lift(b)))

    def Mul(self, a, b):
        if ConcreteDomain.belongto(a):
            if a.getValue() == 0:
                return a
            elif a.getValue() == 1:
                return b
            if ConcreteDomain.belongto(b):
                if b.getValue() == 0:
                    return b
                if b.getValue() == 1:
                    return a
                return ConcreteDomain.Mul(a, b)
        elif ConcreteDomain.belongto(b):
            if b.getValue() == 1:
                return a
        return opt(SymbolicDomain.Mul(self.lift(a), self.lift(b)))

    def Div(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a):
            if a.getValue() == 0:
                return a
            if ConcreteDomain.belongto(b):
                return ConcreteDomain.Div(a, b, unsigned)
        return opt(SymbolicDomain.Div(self.lift(a), self.lift(b), unsigned))

    def Rem(self, a, b, unsigned=False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Rem(a, b, unsigned)
        return opt(SymbolicDomain.Rem(self.lift(a), self.lift(b), unsigned))
