from typing import Union

from slowbeast.domains.concrete_int_float import ConcreteIntFloatDomain
from slowbeast.domains.symbolic import SymbolicDomain
from .expr import Expr
from slowbeast.domains.value import Value
from slowbeast.ir.types import BoolType, IntType, Type
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.domains.concrete_bool import ConcreteBool
from . import SYMCRETE_DOMAIN_KIND


optimize_exprs = True


class ExprOptIntf:
    """
    Expressions optimizer interface
    """

    def optimize(expr, *assumptions) -> "ExprOptIntf":
        """Optimize the expression given the assumptions"""
        return expr


class SymbolicExprOpt(ExprOptIntf):
    def optimize(
        expr: ExprOptIntf, *assumptions
    ) -> Union[ConcreteVal, Expr, ExprOptIntf]:
        if not optimize_exprs:
            return expr

        optexpr = SymbolicDomain.simplify(expr, *assumptions)
        # lower the symbolic expression into a concrete value
        # if possible
        const = SymbolicDomain.to_python_constant(optexpr)
        if const is not None:
            return ConcreteVal(const, optexpr.type())
        return optexpr


def em_optimize_expressions(b: bool = True) -> None:
    global optimize_exprs
    optimize_exprs = b


opt = SymbolicExprOpt.optimize

# FIXME: This domain still has the methods as ExprManager (which it used to be),
# other domains have only static methods...
class SymcreteDomain:
    """
    Takes care of creating (caching and optimizing) expressions.
    The default mode (right now) is just to create Bare
    SMT formulas, but we'll be ready for the future :)
    """

    KIND: int = SYMCRETE_DOMAIN_KIND

    __slots__ = "_names"

    def __init__(self) -> None:
        self._names = {}

    def ConcreteVal(self, c: bool, bw) -> ConcreteBool:
        return ConcreteIntFloatDomain.Value(c, bw)

    def Var(self, name: str, ty: Type):
        assert isinstance(name, str)
        names = self._names
        s = names.get(name)
        if s:
            assert (
                s.type() == ty
            ), f"Creating the same value with different type: {name} ({s.type()} != {ty})"
        else:
            s = SymbolicDomain.Var(name, ty)
            names[name] = s
        assert s, "No var was created"
        return s

    def Bool(self, name: str):
        return self.Var(name, BoolType())

    # def subexpressions(self, expr):
    #    if expr.is_concrete():
    #        yield expr
    #    else:
    #        yield from SymbolicDomain.subexpressions(expr)

    def simplify(self, expr):
        if expr.is_concrete():
            return expr
        return SymbolicExprOpt.optimize(expr)

    def fresh_value(self, name: str, ty: Type) -> Expr:
        assert isinstance(name, str)
        names = self._names
        idx = name.rfind("#")
        if idx == -1:
            origname = name
            cnt = 1
        else:
            origname = name[:idx]
            cnt = int(name[idx + 1 :])
        s = names.get(name)
        while s:
            cnt += 1
            name = f"{origname}#{cnt}"
            s = names.get(name)

        s = SymbolicDomain.Var(name, ty)
        names[name] = s
        return s

    def substitute(self, expr, *vals) -> Union[ConcreteVal, Expr]:
        if ConcreteIntFloatDomain.belongto(expr):
            return expr
        lift = self.lift
        return SymbolicDomain.substitute(expr, *((lift(a), lift(b)) for (a, b) in vals))

    def equals(self, e1: Value, e2: Value):
        """
        Values are syntactically equal
        """
        if ConcreteIntFloatDomain.belongto(e1, e2):
            return e1 == e2
        lift = self.lift
        return lift(e1) == lift(e2)

    def drop_value(self, name) -> None:
        self._names.pop(name)

    def Int1(self, name: str):
        return self.Var(name, IntType(1))

    def Int8(self, name: str):
        return self.Var(name, IntType(8))

    def Int16(self, name: str):
        return self.Var(name, IntType(16))

    def Int32(self, name: str):
        return self.Var(name, IntType(32))

    def Int64(self, name: str):
        return self.Var(name, IntType(64))

    def lift(self, v: Value) -> Expr:
        return SymbolicDomain.lift(v)

    def get_true(self) -> Expr:
        return SymbolicDomain.get_true()

    def get_false(self) -> Expr:
        return SymbolicDomain.get_false()

    def conjunction(self, *args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments
        """
        assert all(map(lambda a: a.is_bool(), args))
        if len(args) == 0:
            return ConcreteIntFloatDomain.get_true()
        if len(args) == 1:
            return args[0]
        if ConcreteIntFloatDomain.belongto(*args):
            return ConcreteIntFloatDomain.conjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.conjunction(*map(lift, args)))

    def disjunction(self, *args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments.
        """
        assert all(map(lambda a: a.is_bool(), args))
        if len(args) == 0:
            return ConcreteIntFloatDomain.get_false()
        if len(args) == 1:
            return args[0]
        if ConcreteIntFloatDomain.belongto(*args):
            return ConcreteIntFloatDomain.disjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.disjunction(*map(lift, args)))

    def Ite(self, c: Value, a, b):
        if ConcreteIntFloatDomain.belongto(c):
            cval = c.value()
            if cval is True:
                return a
            if cval is False:
                return b
            raise RuntimeError(f"Invalid bool: {cval}")
            # return ConcreteIntFloatDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Ite(lift(c), lift(a), lift(b)))

    def And(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a, b):
            return ConcreteIntFloatDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.And(lift(a), lift(b)))

    def Or(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a, b):
            return ConcreteIntFloatDomain.Or(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Or(lift(a), lift(b)))

    def Xor(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a, b):
            return ConcreteIntFloatDomain.Xor(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Xor(lift(a), lift(b)))

    def Not(self, a: Value):
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.Not(a)
        return opt(SymbolicDomain.Not(self.lift(a)))

    def Neg(self, a: Value, isfloat):
        """Return the negated number"""
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.Neg(a, isfloat)
        return opt(SymbolicDomain.Neg(self.lift(a), isfloat))

    def Abs(self, a: Value):
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.Abs(a)
        return opt(SymbolicDomain.Abs(self.lift(a)))

    def FpOp(self, op, val: Value):
        if ConcreteIntFloatDomain.belongto(val):
            return ConcreteIntFloatDomain.FpOp(op, val)
        r = SymbolicDomain.FpOp(op, self.lift(val))
        return opt(r) if r else r  # FpOp may return None

    def ZExt(self, a, b):
        assert ConcreteIntFloatDomain.belongto(b), "Invalid zext argument"
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.ZExt(a, b)
        return opt(SymbolicDomain.ZExt(a, b))

    def SExt(self, a, b):
        assert ConcreteIntFloatDomain.belongto(b), "Invalid sext argument"
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.SExt(a, b)
        return opt(SymbolicDomain.SExt(a, b))

    def Cast(self, a: Value, ty: Type) -> Union[None, Expr, Value]:
        """reinterpret cast"""
        assert isinstance(ty, Type)
        if a.type() == ty:
            return a
        if a.is_pointer():
            # pointer to int or int to pointer (where the int is actually
            # a pointer as we do not change its value)
            return a
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.Cast(a, ty)
        return SymbolicDomain.Cast(a, ty)

    def BitCast(self, a: Value, ty: Type) -> Union[None, Expr, Value]:
        """static cast"""
        assert isinstance(ty, Type)
        if a.type() == ty:
            return a
        if a.is_pointer():
            # pointer to int or int to pointer (where the int is actually
            # a pointer as we do not change its value)
            return a
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.BitCast(a, ty)
        return SymbolicDomain.BitCast(a, ty)

    def Extract(self, a, start, end):
        assert ConcreteIntFloatDomain.belongto(start, end), "Invalid sext argument"
        if ConcreteIntFloatDomain.belongto(a):
            return ConcreteIntFloatDomain.Extract(a, start, end)
        return opt(SymbolicDomain.Extract(a, start, end))

    def Concat(self, *args):
        if ConcreteIntFloatDomain.belongto(*args):
            return ConcreteIntFloatDomain.Concat(*args)
        lift = self.lift
        return opt(SymbolicDomain.Concat(*map(lift, args)))

    def Shl(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Shl(a, b)
        return opt(SymbolicDomain.Shl(self.lift(a), self.lift(b)))

    def AShr(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.AShr(a, b)
        return opt(SymbolicDomain.AShr(self.lift(a), self.lift(b)))

    def LShr(self, a: Value, b: Value):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.LShr(a, b)
        return opt(SymbolicDomain.LShr(self.lift(a), self.lift(b)))

    ##
    # Relational operators

    def Le(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Le(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Le(lift(a), lift(b), unsigned, isfloat))

    def Lt(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Lt(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Lt(lift(a), lift(b), unsigned, isfloat))

    def Ge(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Ge(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Ge(lift(a), lift(b), unsigned, isfloat))

    def Gt(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
                return ConcreteIntFloatDomain.Gt(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Gt(lift(a), lift(b), unsigned, isfloat))

    def Eq(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Eq(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Eq(lift(a), lift(b), unsigned, isfloat))

    def Ne(self, a: Value, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a) and ConcreteIntFloatDomain.belongto(b):
            return ConcreteIntFloatDomain.Ne(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Ne(lift(a), lift(b), unsigned, isfloat))

    ##
    # Artihmetic operations
    def Add(self, a, b, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a):
            if a.value() == 0:
                return b
            if ConcreteIntFloatDomain.belongto(b):
                if b.value() == 0:
                    return a
                return ConcreteIntFloatDomain.Add(a, b, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Add(lift(a), lift(b), isfloat))

    def Sub(self, a, b: Value, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(b):
            if b.value() == 0:
                return a
            if ConcreteIntFloatDomain.belongto(a):
                return ConcreteIntFloatDomain.Sub(a, b, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Sub(lift(a), lift(b), isfloat))

    def Mul(self, a, b, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a):
            if a.value() == 0:
                return a
            if a.value() == 1:
                return b
            if ConcreteIntFloatDomain.belongto(b):
                if b.value() == 0:
                    return b
                if b.value() == 1:
                    return a
                return ConcreteIntFloatDomain.Mul(a, b, isfloat)
        elif ConcreteIntFloatDomain.belongto(b):
            if b.value() == 1:
                return a
        lift = self.lift
        return opt(SymbolicDomain.Mul(lift(a), lift(b), isfloat))

    def Div(self, a, b: Value, unsigned: bool = False, isfloat: bool = False):
        if ConcreteIntFloatDomain.belongto(a):
            if a.value() == 0:
                return a
            if ConcreteIntFloatDomain.belongto(b):
                return ConcreteIntFloatDomain.Div(a, b, unsigned, isfloat)
        lift = self.lift
        return opt(SymbolicDomain.Div(lift(a), lift(b), unsigned, isfloat))

    def Rem(self, a: Value, b: Value, unsigned: bool = False):
        if ConcreteIntFloatDomain.belongto(a, b):
            return ConcreteIntFloatDomain.Rem(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Rem(lift(a), lift(b), unsigned))
