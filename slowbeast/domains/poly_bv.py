from typing import Optional

from z3 import (
    is_and,
    is_or,
    is_not,
    is_eq,
    is_app_of,
    Z3_OP_SLEQ,
    Z3_OP_SLT,
    Z3_OP_ULEQ,
    Z3_OP_ULT,
    Z3_OP_SGEQ,
    Z3_OP_SGT,
    Z3_OP_UGEQ,
    Z3_OP_UGT,
    simplify,
    is_bv,
    is_bool,
    Z3_OP_BADD,
    Z3_OP_BMUL,
    is_const,
    is_bv_value,
    Not,
    ULE as BVULE,
    ULT as BVULT,
    UGE as BVUGE,
    UGT as BVUGT,
)

from slowbeast.domains.symbolic_helpers import (
    _bv_to_bool,
    mk_or,
    mk_and,
    bv_const,
    bool_to_bv,
)
from slowbeast.solvers.arithformula import ArithFormula, Monomial, Polynomial


def _expr_op_to_formula_op(expr) -> Optional[int]:
    if is_and(expr):
        return ArithFormula.AND
    if is_or(expr):
        return ArithFormula.OR
    if is_not(expr):
        return ArithFormula.NOT

    if is_eq(expr):
        return ArithFormula.EQ
    if is_app_of(expr, Z3_OP_SLEQ):
        return ArithFormula.SLE
    if is_app_of(expr, Z3_OP_SLT):
        return ArithFormula.SLT
    if is_app_of(expr, Z3_OP_ULEQ):
        return ArithFormula.ULE
    if is_app_of(expr, Z3_OP_ULT):
        return ArithFormula.ULT
    if is_app_of(expr, Z3_OP_SGEQ):
        return ArithFormula.SGE
    if is_app_of(expr, Z3_OP_SGT):
        return ArithFormula.SGT
    if is_app_of(expr, Z3_OP_UGEQ):
        return ArithFormula.UGE
    if is_app_of(expr, Z3_OP_UGT):
        return ArithFormula.UGT

    # raise NotImplementedError(f"Unhandled operation: {expr}")
    return None


class BVMonomial(Monomial):
    """
    Helper class for representing formulas in LIA or BV theory.
    This class makes it easy to work with commutative expressions
    by merging the operands into sets (if the operation is commutative).
    """

    def __init__(self, *variabl) -> None:
        super().__init__(*variabl)

    def create(expr: Monomial):
        raise NotImplementedError("Must be overridden")

    def expr(self):
        "Transform to Z3 expressions"
        V = self.vars
        if not V:
            return None
        it = iter(V.items())
        m, c = next(it)
        expr = m
        while c > 1:
            expr = expr * m
            c -= 1
        for m, c in it:
            while c > 0:
                expr = expr * m
                c -= 1
        return simplify(expr)


class BVPolynomial(Polynomial):
    """
    Helper class for representing formulas in LIA or BV theory.
    This class makes it easy to work with commutative expressions
    by merging the operands into sets (if the operation is commutative).
    """

    def __init__(self, bw, *elems) -> None:
        self._bw = bw  # bitwidth
        super().__init__(*elems)

    def bitwidth(self):
        return self._bw

    def copy(self) -> "BVPolynomial":
        P = type(self)(self._bw)
        P.monomials = {m.copy(): c for m, c in self.monomials.items()}
        return P

    def clean_copy(self) -> "BVPolynomial":
        return type(self)(self._bw)

    def _create_coefficient(self, c, m):
        """
        Create a coefficient 'c' to monomial 'm'.
        This method can be overriden, e.g., to have the
        coefficients modulo something.
        """
        if is_bv(c):
            return c
        return bv_const(c, self._bw)

    def _coefficient_is_zero(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        assert is_bv(c), c
        val = simplify(c == 0)
        assert is_bool(val), val
        return val.__bool__()

    def _coefficient_is_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        assert is_bv(c), c
        val = simplify(c == 1)
        assert is_bool(val), val
        return val.__bool__()

    def _coefficient_is_minus_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        assert is_bv(c), c
        val = simplify(c == -1)
        assert is_bool(val), val
        return val.__bool__()

    def _simplify_coefficient(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return simplify(c)

    def create(expr: Polynomial):
        bw = 1 if is_bool(expr) else expr.size()
        if is_app_of(expr, Z3_OP_BADD):
            return BVPolynomial(bw, *(BVPolynomial.create(e) for e in expr.children()))
        elif is_app_of(expr, Z3_OP_BMUL):
            pols = [BVPolynomial.create(e) for e in expr.children()]
            P = pols[0]
            for i in range(1, len(pols)):
                P.mul(pols[i])
            return P
        # elif is_app_of(expr, Z3_OP_CONCAT) or\
        #        is_app_of(expr, Z3_OP_SIGN_EXT) or\
        #        is_app_of(expr, Z3_OP_ZERO_EXT) or\
        #        is_app_of(expr, Z3_OP_EXTRACT):
        #    # TODO: check that these operations are applied to const?
        #    return BVPolynomial(bw, BVMonomial((expr, 1)))
        # elif is_app_of(expr, Z3_OP_BUREM) or\
        #        is_app_of(expr, Z3_OP_BUREM_I) or\
        #        is_app_of(expr, Z3_OP_BSREM) or\
        #        is_app_of(expr, Z3_OP_BSREM_I) or\
        #        is_app_of(expr, Z3_OP_BUDIV) or\
        #        is_app_of(expr, Z3_OP_BSDIV) or\
        #        is_app_of(expr, Z3_OP_BUDIV_I) or\
        #        is_app_of(expr, Z3_OP_BSDIV_I):
        #    # TODO: check that these operations are applied to const?
        #    return BVPolynomial(bw, BVMonomial((expr, 1)))
        elif is_const(expr):
            if is_bv_value(expr):
                return BVPolynomial(bw, (expr, BVMonomial()))
            return BVPolynomial(bw, BVMonomial((expr, 1)))

        return BVPolynomial(bw, BVMonomial((expr, 1)))
        # raise NotImplementedError(f"Unhandeld expression: {expr}")

    def expr(self):
        "Transform to Z3 expressions"
        M = self.monomials
        if not M:
            return bv_const(0, self._bw)

        it = iter(M.items())
        m, c = next(it)
        mexpr = bool_to_bv(m.expr())
        expr = c if mexpr is None else c * mexpr
        for m, c in it:
            mexpr = m.expr()
            expr += c if mexpr is None else c * mexpr
        return simplify(expr)


class BVFormula(ArithFormula):
    """
    Helper class for representing formulas in LIA or BV theory.
    This class makes it easy to work with commutative expressions
    by merging the operands into sets (if the operation is commutative).
    """

    def __init__(self, ty: ArithFormula, *operands) -> None:
        super().__init__(ty, *operands)

    def create(expr: ArithFormula) -> Optional[ArithFormula]:
        chlds = expr.children()
        op = _expr_op_to_formula_op(expr)
        if chlds:
            if op is None:
                # it is a polynomial
                return BVFormula(ArithFormula.POLYNOM, BVPolynomial.create(expr))
            isac = ArithFormula.op_is_assoc_and_comm(op)
            formula = BVFormula(op, None)
            for c in chlds:
                f = BVFormula.create(c)
                if f is None:
                    return None
                if isac and op == _expr_op_to_formula_op(c):
                    for fc in f.children():
                        formula.add_child(fc)
                else:
                    formula.add_child(f)
            return formula
        # return BVFormula(_expr_op_to_formula_op(expr), None,
        #                 *(BVFormula.create(c) for c in chlds))
        if not is_bv(expr):
            if is_bool(expr):
                return BVFormula(ArithFormula.BOOLEAN, expr)
            return None  # it is no bitvector, we cannot do a polynom from it
        return BVFormula(ArithFormula.POLYNOM, BVPolynomial.create(expr))

    def value_equals(self, x):
        v = self._value
        if v is None:
            return False
        return is_bv_value(v) and v.as_long() == x

    def expr(self):
        "Convert this object into expression for solver"
        ty = self._ty
        if ty == ArithFormula.BOOLEAN:
            return self._value
        if ty == ArithFormula.POLYNOM:
            return self._value.expr()
        if ty == ArithFormula.AND:
            return mk_and(*(c.expr() for c in self._children))
        if ty == ArithFormula.OR:
            return mk_or(*(c.expr() for c in self._children))
        if ty == ArithFormula.NOT:
            assert len(self._children) == 1
            return Not(_bv_to_bool(self._children[0].expr()))

        chlds = self._children
        if len(chlds) != 2:
            raise NotImplementedError(f"Not implemented yet: {self}")
            return None
        if ty == ArithFormula.EQ:
            return chlds[0].expr() == chlds[1].expr()
        if ty == ArithFormula.SLE:
            return chlds[0].expr() <= chlds[1].expr()
        if ty == ArithFormula.SLT:
            return chlds[0].expr() < chlds[1].expr()
        if ty == ArithFormula.SGE:
            return chlds[0].expr() >= chlds[1].expr()
        if ty == ArithFormula.SGT:
            return chlds[0].expr() > chlds[1].expr()
        if ty == ArithFormula.ULE:
            return BVULE(chlds[0].expr(), chlds[1].expr())
        if ty == ArithFormula.ULT:
            return BVULT(chlds[0].expr(), chlds[1].expr())
        if ty == ArithFormula.UGE:
            return BVUGE(chlds[0].expr(), chlds[1].expr())
        if ty == ArithFormula.UGT:
            return BVUGT(chlds[0].expr(), chlds[1].expr())

        raise NotImplementedError(f"Not implemented yet: {self}")
        return None
