from typing import Generator, Union, Optional, List, Tuple, Dict

from z3 import (
    is_bv_value,
    And,
    is_eq,
    is_and,
    is_or,
    is_not,
    is_app_of,
    Z3_OP_EQ,
    Z3_OP_SLEQ,
    Z3_OP_ULEQ,
    Z3_OP_SGEQ,
    Z3_OP_UGEQ,
    Z3_OP_SLT,
    Z3_OP_ULT,
    Z3_OP_SGT,
    Z3_OP_UGT,
    Z3_OP_BMUL,
)

from slowbeast.domains import SYMBOLIC_DOMAIN_KIND
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.concrete import concrete_value
from slowbeast.domains.symbolic_helpers import (
    subexpressions,
    symbols,
    to_cnf,
    rewrite_simplify,
    split_clauses,
    solver_to_sb_type,
    _is_symbol,
    mk_or,
)
from slowbeast.domains.symbolic_rewriting import (
    rewrite_polynomials,
    get_eqs_from_ineqs,
    eqs_from_ineqs,
    replace_arith_ops,
    reduce_eq_bitwidth,
    reduce_arith_bitwidth,
)
from slowbeast.domains.value import Value
from slowbeast.ir.types import Type
from z3.z3 import BitVecRef, BoolRef, FPRef


class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """

    KIND: int = SYMBOLIC_DOMAIN_KIND

    def __init__(self, e: Union[BoolRef, FPRef, BitVecRef], t: Type) -> None:
        assert not isinstance(e, int), e
        assert isinstance(t, Type), t
        super().__init__(e, t)

    def is_nondet_load(self) -> bool:
        return False

    def is_nondet_instr_result(self) -> bool:
        return False

    def is_future(self) -> bool:
        return False

    def name(self):
        return str(self._value)

    def is_concrete(self) -> bool:
        return False

    def is_symbolic(self) -> bool:
        return True

    def as_value(self) -> str:
        return str(self)

    def subexpressions(self) -> Generator[Union[ConcreteVal, "Expr"], None, None]:
        """Traverse the expression and return its all subexpressions"""
        return (
            concrete_value(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in subexpressions(self.unwrap())
        )

    def children(self) -> Generator[Union[ConcreteVal, "Expr"], None, None]:
        """
        Get the children (1st-level subexpressions) of this expression.
        E.g. for And(a, b) this method returns [a, b].
        """
        return (
            concrete_value(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in self.unwrap().children()
        )

    def symbols(self) -> Generator["Expr", None, None]:
        """
        Get the symbols used in this expression.
        E.g. for And(a, 3*b) this method returns [a, b].
        """
        return (Expr(s, solver_to_sb_type(s)) for s in symbols(self.unwrap()))

    def is_symbol(self):
        return _is_symbol(self._value)

    def to_cnf(self) -> "Expr":
        """
        Get the expression in CNF form.
        """
        return Expr(And(*to_cnf(self.unwrap())), self.type())

    def rewrite_and_simplify(self) -> "Expr":
        """
        Get the expression in CNF form.
        """
        return Expr(
            mk_or(*(And(*c) for c in rewrite_simplify(self._value))), self.type()
        )

    def split_clauses(self) -> "Expr":
        """
        Get the expression in CNF form.
        """
        return Expr(mk_or(*(And(*c) for c in split_clauses(self._value))), self.type())

    def reduce_eq_bitwidth(self, bw) -> Optional["Expr"]:
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr = reduce_eq_bitwidth(self.unwrap(), bw)
        if expr is None:
            return None
        ty = solver_to_sb_type(expr)
        assert ty.bitwidth() <= bw
        return Expr(expr, ty)

    def reduce_arith_bitwidth(self, bw) -> Optional["Expr"]:
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr = reduce_arith_bitwidth(self.unwrap(), bw)
        if expr is None:
            return None
        ty = solver_to_sb_type(expr)
        assert ty.bitwidth() <= bw
        return Expr(expr, ty)

    def rewrite_polynomials(self, from_exprs) -> "Expr":
        expr = rewrite_polynomials(
            self.unwrap(), map(lambda x: x.unwrap(), from_exprs) if from_exprs else None
        )
        if expr is None:
            return self
        return Expr(expr, self.type())

    def infer_equalities(self) -> List["Expr"]:
        cnf = self.to_cnf().unwrap()  # we need clauses
        # get equalities  from comparison
        eqs = set(e for c1, c2, e in get_eqs_from_ineqs(cnf))
        # get equalities right from the formula
        eqs.update(e for e in cnf.children() if is_eq(e))
        return [Expr(expr, solver_to_sb_type(expr)) for expr in eqs]

    def eqs_from_ineqs(self) -> "Expr":
        expr = eqs_from_ineqs(self.to_cnf().unwrap())
        if expr is None:
            return self
        return Expr(expr, self.type())

    def replace_arith_ops(
        self,
    ) -> Tuple[Optional["Expr"], Optional[Dict["Expr", "Expr"]]]:
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr, subs = replace_arith_ops(self.unwrap())
        if expr is None:
            return None, None
        return Expr(expr, self.type()), {
            Expr(k, solver_to_sb_type(k)): Expr(v, solver_to_sb_type(v))
            for k, v in subs.items()
        }

    def is_and(self) -> bool:
        return is_and(self.unwrap())

    def is_or(self):
        return is_or(self.unwrap())

    def is_not(self):
        return is_not(self.unwrap())

    def is_eq(self):
        return is_app_of(self._value, Z3_OP_EQ)

    def is_le(self):
        return is_app_of(self._value, Z3_OP_SLEQ) or is_app_of(self._value, Z3_OP_ULEQ)

    def is_ge(self):
        return is_app_of(self._value, Z3_OP_SGEQ) or is_app_of(self._value, Z3_OP_UGEQ)

    def is_lt(self):
        return is_app_of(self._value, Z3_OP_SLT) or is_app_of(self._value, Z3_OP_ULT)

    def is_gt(self):
        return is_app_of(self._value, Z3_OP_SGT) or is_app_of(self._value, Z3_OP_UGT)

    def is_sle(self):
        return is_app_of(self._value, Z3_OP_SLEQ)

    def is_sge(self):
        return is_app_of(self._value, Z3_OP_SGEQ)

    def is_slt(self):
        return is_app_of(self._value, Z3_OP_SLT)

    def is_sgt(self):
        return is_app_of(self._value, Z3_OP_SGT)

    def is_ule(self):
        return is_app_of(self._value, Z3_OP_ULEQ)

    def is_uge(self):
        return is_app_of(self._value, Z3_OP_UGEQ)

    def is_ult(self):
        return is_app_of(self._value, Z3_OP_ULT)

    def is_ugt(self):
        return is_app_of(self._value, Z3_OP_UGT)

    def is_mul(self):
        # or is_app_of(self._value, Z3_OP_MUL)
        return is_app_of(self._value, Z3_OP_BMUL)

    def __hash__(self):
        return self._value.__hash__()

    def __eq__(self, rhs):
        return self._value == rhs._value if isinstance(rhs, Expr) else False

    def __repr__(self) -> str:
        return f"<{self._value}:{self.type()}>"


class NondetInstrResult(Expr):
    """Expression representing a result of instruction that is unknown - non-deterministic"""

    __slots__ = "_instr"

    def __init__(self, e, t: Type, instr) -> None:
        super().__init__(e, t)
        self._instr = instr

    def is_nondet_instr_result(self) -> bool:
        return True

    def instruction(self):
        return self._instr

    @staticmethod
    def from_expr(expr: Expr, instr) -> "NondetInstrResult":
        assert isinstance(expr, Expr)
        return NondetInstrResult(expr.unwrap(), expr.type(), instr)

    def __repr__(self) -> str:
        return f"{self._instr.as_value()}={Expr.__repr__(self)}"


class NondetLoad(NondetInstrResult):
    __slots__ = "alloc"

    def __init__(self, e, t: Type, load, alloc) -> None:
        super().__init__(e, t, load)
        self.alloc = alloc

    def is_nondet_load(self) -> bool:
        return True

    def load(self):
        return self._instr

    @staticmethod
    def from_expr(expr: Expr, load, alloc) -> "NondetLoad":
        assert isinstance(expr, Expr)
        return NondetLoad(expr.unwrap(), expr.type(), load, alloc)

    def rhs_repr(self) -> str:
        return Expr.__repr__(self)

    def __repr__(self) -> str:
        return f"L({self.alloc.as_value()})={Expr.__repr__(self)}"


class Future(Expr):
    """
    Represents a value of non-executed operation (instruction)
    (that is going to be executed as a feedback to the developement of the search
    """

    __slots__ = "_instr", "_state"

    def __init__(self, e, t: Type, instr, state) -> None:
        super().__init__(e, t)
        # to which instr we assigned the nondet value
        self._instr = instr
        # stored state
        self._state = state

    def is_future(self) -> bool:
        return True

    def state(self):
        return self._state

    @staticmethod
    def from_expr(expr: Expr, instr, state) -> "Future":
        assert isinstance(expr, Expr)
        return Future(expr.unwrap(), expr.type(), instr)

    def __repr__(self) -> str:
        return f"future({self._instr.as_value()})={super().__repr__()}"
