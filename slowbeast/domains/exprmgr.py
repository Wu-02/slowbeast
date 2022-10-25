from typing import Union

from slowbeast.domains.concrete import ConcreteDomain
from slowbeast.domains.symbolic import SymbolicDomain
from .expr import Expr
from slowbeast.domains.value import Value
from slowbeast.ir.types import Type
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.util.debugging import FIXME


optimize_exprs = True


class ExprOptIntf:
    """
    Expressions optimizer interface
    """

    def optimize(expr, *assumptions) -> "ExprOptIntf":
        """Optimize the expression given the assumptions"""
        return expr


class SymbolicExprOpt(ExprOptIntf):
    def optimize(expr: Expr, *assumptions) -> Union[ConcreteVal, Expr]:
        if not optimize_exprs:
            return expr

        optexpr = SymbolicDomain.simplify(expr, *assumptions)
        # lower the symbolic expression into a concrete value
        # if possible
        const = SymbolicDomain.to_python_constant(optexpr)
        if const is not None:
            ConcreteDomain.Value(const, optexpr.type().bitwidth())
        return optexpr


def em_optimize_expressions(b: bool = True) -> None:
    global optimize_exprs
    optimize_exprs = b


opt = SymbolicExprOpt.optimize

# FIXME: This domain still has the methods as ExprManager (which it used to be),
# other domains have only static methods...
class ExpressionManager:
    """
    Takes care of creating expressions, including lifting/lowering arguments
    and expressions themselves.
    """

    __slots__ = "_names"

    def __init__(self) -> None:
        self._names = {}

    def ConcreteVal(self, c, bw: int) -> ConcreteVal:
        return ConcreteDomain.Value(c, bw)

    # def Var(self, name: str, ty: Type):
    #    assert isinstance(name, str)
    #    names = self._names
    #    s = names.get(name)
    #    if s:
    #        assert (
    #            s.type() == ty
    #        ), f"Creating the same value with different type: {name} ({s.type()} != {ty})"
    #    else:
    #        s = SymbolicDomain.Var(name, ty)
    #        names[name] = s
    #    assert s, "No var was created"
    #    return s

    # def Bool(self, name: str):
    #    return self.Var(name, BoolType())

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

        s = SymbolicDomain.Value(name, ty)
        names[name] = s
        return s

    def substitute(self, expr, *vals) -> Union[ConcreteVal, Expr]:
        if isinstance(expr, ConcreteVal):
            return expr
        lift = self.lift
        return SymbolicDomain.substitute(expr, *((lift(a), lift(b)) for (a, b) in vals))

    def drop_value(self, name) -> None:
        self._names.pop(name)

    # def Int1(self, name: str):
    #    return self.Var(name, BitVecType(1))

    # def Int8(self, name: str):
    #    return self.Var(name, BitVecType(8))

    # def Int16(self, name: str):
    #    return self.Var(name, BitVecType(16))

    # def Int32(self, name: str):
    #    return self.Var(name, BitVecType(32))

    # def Int64(self, name: str):
    #    return self.Var(name, BitVecType(64))

    def lift(self, v: Value) -> Expr:
        return SymbolicDomain.lift(v)

    def get_true(self) -> Expr:
        """Get symbol "true" """
        FIXME("Rename me, it's not clear if I should be symbolic or concrete")
        return SymbolicDomain.get_true()

    def get_false(self) -> Expr:
        FIXME("Rename me, it's not clear if I should be symbolic or concrete")
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
            return ConcreteDomain.get_true()
        if len(args) == 1:
            return args[0]
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
        assert all(map(lambda a: a.is_bool(), args))
        if len(args) == 0:
            return ConcreteDomain.get_false()
        if len(args) == 1:
            return args[0]
        if ConcreteDomain.belongto(*args):
            return ConcreteDomain.disjunction(*args)
        lift = self.lift
        return opt(SymbolicDomain.disjunction(*map(lift, args)))

    def Ite(self, c: Value, a: Value, b: Value):
        if ConcreteDomain.belongto(c):
            cval = c.value()
            if cval is True:
                return a
            if cval is False:
                return b
            raise RuntimeError(f"Invalid bool: {cval}")
            # return ConcreteDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Ite(lift(c), lift(a), lift(b)))

    def And(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.And(a, b)
        lift = self.lift
        return opt(SymbolicDomain.And(lift(a), lift(b)))

    def Or(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Or(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Or(lift(a), lift(b)))

    def Xor(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Xor(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Xor(lift(a), lift(b)))

    def Not(self, a: Value):
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Not(a)
        return opt(SymbolicDomain.Not(self.lift(a)))

    def Neg(self, a: Value):
        """Return the negated number"""
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Neg(a)
        return opt(SymbolicDomain.Neg(self.lift(a)))

    def Abs(self, a: Value):
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Abs(a)
        return opt(SymbolicDomain.Abs(self.lift(a)))

    def FpOp(self, op, val: Value):
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.FpOp(op, val)
        r = SymbolicDomain.FpOp(op, self.lift(val))
        return opt(r) if r else r  # FpOp may return None

    def Extend(self, a: Value, b: int, unsigned: bool):
        assert isinstance(b, int), f"Invalid extend argument: {b}"
        assert isinstance(unsigned, bool), f"Invalid extend argument: {unsigned}"
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Extend(a, b, unsigned)
        return opt(SymbolicDomain.Extend(a, b, unsigned))

    def Cast(self, a: Value, ty: Type) -> Union[None, Expr, Value]:
        """reinterpret cast"""
        assert isinstance(ty, Type)
        if a.type() == ty:
            return a
        if a.is_pointer():
            # pointer to int or int to pointer (where the int is actually
            # a pointer as we do not change its value)
            return a
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Cast(a, ty)
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
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.BitCast(a, ty)
        return SymbolicDomain.BitCast(a, ty)

    def Extract(self, a, start, end):
        assert ConcreteDomain.belongto(start), start
        assert ConcreteDomain.belongto(end), end
        if isinstance(a, ConcreteVal):
            return ConcreteDomain.Extract(a, start, end)
        return opt(SymbolicDomain.Extract(a, start, end))

    def Concat(self, *args):
        if all(map(lambda a: isinstance(a, ConcreteVal), args)):
            return ConcreteDomain.Concat(*args)
        lift = self.lift
        return opt(SymbolicDomain.Concat(*map(lift, args)))

    def Shl(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Shl(a, b)
        return opt(SymbolicDomain.Shl(self.lift(a), self.lift(b)))

    def AShr(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.AShr(a, b)
        return opt(SymbolicDomain.AShr(self.lift(a), self.lift(b)))

    def LShr(self, a: Value, b: Value):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.LShr(a, b)
        return opt(SymbolicDomain.LShr(self.lift(a), self.lift(b)))

    ##
    # Relational operators

    def Le(self, a: Value, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Le(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Le(lift(a), lift(b), unsigned))

    def Lt(self, a: Value, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Lt(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Lt(lift(a), lift(b), unsigned))

    def Ge(self, a: Value, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Ge(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Ge(lift(a), lift(b), unsigned))

    def Gt(self, a: Value, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Gt(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Gt(lift(a), lift(b), unsigned))

    def Eq(self, a: Value, b: Value, unsigned: bool = False):
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Eq(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Eq(lift(a), lift(b), unsigned))

    def Ne(self, a: Value, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal) and isinstance(b, ConcreteVal):
            return ConcreteDomain.Ne(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Ne(lift(a), lift(b), unsigned))

    ##
    # Artihmetic operations
    def Add(self, a, b):
        if isinstance(a, ConcreteVal):
            if a.value() == 0:
                return b
            if isinstance(b, ConcreteVal):
                if b.value() == 0:
                    return a
                return ConcreteDomain.Add(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Add(lift(a), lift(b)))

    def Sub(self, a, b: Value):
        if isinstance(b, ConcreteVal):
            if b.value() == 0:
                return a
            if isinstance(a, ConcreteVal):
                return ConcreteDomain.Sub(a, b)
        lift = self.lift
        return opt(SymbolicDomain.Sub(lift(a), lift(b)))

    def Mul(self, a, b):
        if isinstance(a, ConcreteVal):
            if a.value() == 0:
                return a
            if a.value() == 1:
                return b
            if isinstance(b, ConcreteVal):
                if b.value() == 0:
                    return b
                if b.value() == 1:
                    return a
                return ConcreteDomain.Mul(a, b)
        elif isinstance(b, ConcreteVal):
            if b.value() == 1:
                return a
        lift = self.lift
        return opt(SymbolicDomain.Mul(lift(a), lift(b)))

    def Div(self, a, b: Value, unsigned: bool = False):
        if isinstance(a, ConcreteVal):
            if a.value() == 0:
                return a
            if isinstance(b, ConcreteVal):
                return ConcreteDomain.Div(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Div(lift(a), lift(b), unsigned))

    def Rem(self, a: Value, b: Value, unsigned: bool = False):
        if ConcreteDomain.belongto(a, b):
            return ConcreteDomain.Rem(a, b, unsigned)
        lift = self.lift
        return opt(SymbolicDomain.Rem(lift(a), lift(b), unsigned))