from z3 import (
    is_const,
    is_app_of,
    Z3_OP_ZERO_EXT,
    Z3_OP_SIGN_EXT,
    Z3_OP_CONCAT,
    Z3_OP_EXTRACT,
    Z3_OP_BMUL,
    SignExt as BVSExt,
    Concat as BVConcat,
    is_and,
    is_or,
    is_not,
    Not,
    Z3_OP_BADD,
    is_eq,
    is_distinct,
    is_bv_value,
    simplify,
    If,
    Tactic,
    Z3_OP_SLEQ,
    Z3_OP_ULEQ,
    ULE as BVULE,
    UGE as BVUGE,
    And,
    Then,
    With,
    BitVec,
    substitute,
    Extract as BVExtract,
    ZeroExt as BVZExt,
    is_bv,
    Or,
)

from slowbeast.domains.poly_bv import BVPolynomial, BVFormula
from slowbeast.domains.symbolic_helpers import mk_and, mk_or, mk_add, mk_mul, bv_const
from slowbeast.solvers.arithformula import ArithFormula


def is_lit(e):
    return is_const(e) or (
        (
            is_app_of(e, Z3_OP_ZERO_EXT)
            or is_app_of(e, Z3_OP_SIGN_EXT)
            or is_app_of(e, Z3_OP_CONCAT)
            or is_app_of(e, Z3_OP_EXTRACT)
        )
        and is_lit(e.children()[0])
    )


def _is_const_mul(expr):
    chld = expr.children()
    return is_app_of(expr, Z3_OP_BMUL) and is_lit(chld[0]) and is_lit(chld[1])


def _get_replacable(expr, atoms) -> None:
    chld = expr.children()
    if _is_const_mul(expr):
        v = atoms.setdefault(expr, 0)
        atoms[expr] = v + 1
        return
    for c in chld:
        _get_replacable(c, atoms)


def _desimplify_ext(expr):
    "replace concat with singext if possible -- due to debugging"
    if is_app_of(expr, Z3_OP_CONCAT):
        chld = expr.children()
        c0 = chld[0]
        if is_app_of(c0, Z3_OP_EXTRACT):
            params = c0.params()
            if (
                params[0] == params[1] == (chld[-1].size() - 1)
                and c0.children()[0] == chld[-1]
            ):
                if all(map(lambda e: e == c0, chld[1:-1])):
                    return BVSExt(expr.size() - chld[-1].size(), chld[-1])
        des = [_desimplify_ext(c) for c in chld]
        assert len(des) == len(chld)
        assert len(des) > 1
        return BVConcat(des)
    else:
        if is_and(expr):
            return mk_and(*(_desimplify_ext(c) for c in expr.children()))
        elif is_or(expr):
            return mk_or(*(_desimplify_ext(c) for c in expr.children()))
        elif is_not(expr):
            return Not(*(_desimplify_ext(c) for c in expr.children()))
        elif is_app_of(expr, Z3_OP_BADD):
            return mk_add(*(_desimplify_ext(c) for c in expr.children()))
        elif is_app_of(expr, Z3_OP_BMUL):
            return mk_mul(*(_desimplify_ext(c) for c in expr.children()))
        elif is_app_of(expr, Z3_OP_CONCAT):
            return BVConcat(*(_desimplify_ext(c) for c in expr.children()))
        elif is_eq(expr):
            dc = (_desimplify_ext(c) for c in expr.children())
            return next(dc) == next(dc)
        elif is_distinct(expr):
            dc = (_desimplify_ext(c) for c in expr.children())
            return next(dc) != next(dc)
        else:
            assert not is_app_of(expr, Z3_OP_CONCAT), expr
            return expr.decl()(*(_desimplify_ext(c) for c in expr.children()))
            return expr


def _rewrite_sext(expr):
    "replace sext(x + c) with sext(x) + c if possible"
    if is_const(expr):
        return expr
    chld = expr.children()
    # Do we want to recurse also into operands of == and !=?
    if is_app_of(expr, Z3_OP_SIGN_EXT):
        c0 = chld[0]
        if is_app_of(c0, Z3_OP_BADD):
            c0chld = c0.children()
            if len(c0chld) == 2:
                c, x = c0chld[0], c0chld[1]
                if not is_bv_value(c):
                    c, x = x, c
                if is_bv_value(c) and is_const(x):
                    # expr = sext(x + c)
                    bw = c.size()
                    ebw = expr.size()
                    # expr = sext(x + 1)
                    if simplify(c == 1).__bool__():
                        return If(
                            x != 2 ** (bw - 1) - 1,
                            # BVSExt(ebw - bw, x) + BVZExt(ebw - bw, c),
                            # expr)
                            BVSExt(ebw - bw, x) + bv_const(1, ebw),
                            simplify(BVSExt(ebw - bw, bv_const(2**bw - 1, bw) + 1)),
                        )
                    # expr = sext(x + (-1))
                    elif simplify(c == -1).__bool__():
                        return If(
                            x != 2 ** (bw - 1),
                            # BVSExt(ebw - bw, x) + BVSExt(ebw - bw, c),
                            # expr)
                            BVSExt(ebw - bw, x) + bv_const(-1, ebw),
                            simplify(BVSExt(ebw - bw, bv_const(2**bw - 1, bw) - 1)),
                        )
                    # FIXME: do this for generic values
        return expr
    else:
        red = (_rewrite_sext(c) for c in chld)
        if is_and(expr):
            return mk_and(*red)
        elif is_or(expr):
            return mk_or(*red)
        elif is_not(expr):
            return Not(*red)
        elif is_app_of(expr, Z3_OP_CONCAT):
            return BVConcat(*red)
        elif is_app_of(expr, Z3_OP_BADD):
            return mk_add(*red)
        elif is_app_of(expr, Z3_OP_BMUL):
            return mk_mul(*red)
        elif is_eq(expr):
            return next(red) == next(red)
        elif is_distinct(expr):
            return next(red) != next(red)
        else:
            return expr


def _get_common_monomials(P1, P2, same_coef: bool = False):
    monomials = []
    for p1m, c1 in P1.monomials.items():
        c2 = P2.get_coef(p1m)
        if c2 is None:
            continue
        if not same_coef or (c1.size() == c2.size() and simplify(c1 == c2).__bool__()):
            monomials.append(p1m)
    return monomials


class PolynomialSimplifier:
    def __init__(self, *args) -> None:
        # these polynomials we'll use to simplify the given formula
        self.polynomials = [*args]
        # index of a polynomial and polynomials that we substitued into other polynomials -- to prevent cycles
        # FIXME: we do not use it right now...
        self.used = {}

    def add_poly(self, *ps) -> None:
        self.polynomials.extend(*ps)

    def _simplify_polynomial_formula(self, formula) -> bool:
        # print("> SIMPLIFY", formula)
        # print("> WITH")
        # for p in self.polynomials:
        #    print('  ', p)
        # print('---')
        polynoms = self.polynomials
        assert formula.is_poly(), formula
        P = formula[0]
        for p in polynoms:
            me = p.max_degree_elems()
            if len(me) != 1:
                # FIXME: we should keep track of polynomials that we substitued
                # to not to get into a cycle
                common = _get_common_monomials(p, P, same_coef=True)
                if common:  # and all(map(lambda c: c in common, me)):
                    p1, p2 = p.split(common)
                    p1.change_sign()
                    P.add(p1)
                    P.add(p2)
                    continue
                mP = P.copy()
                mP.change_sign()
                common = _get_common_monomials(p, mP, same_coef=True)
                if common:  # and all(map(lambda c: c in common, me)):
                    p1, p2 = p.split(common)
                    p2.change_sign()
                    P.add(p1)
                    P.add(p2)
                    continue
                continue
            # the rest of the polynomial must have a lesser degree now
            # so perform the substitution of the monomial with the maximal
            # degree
            mme = me[0]
            for monomial, coef in P:
                # mc = P.get_coef(monomial)
                # mec = p.get_coef(mme)
                if not P.is_normed(monomial):
                    continue  # FOR NOW
                if mme.divides(monomial):
                    # FIXME: multiply with the coefficient!
                    r = BVPolynomial(P.bitwidth(), monomial.divided(mme))
                    p1, p2 = p.split([mme])
                    p2.change_sign()
                    r.mul(p2)  # do the substitution
                    P.pop(monomial)
                    P.add(r)
                    # we changed the polynomial, we cannot iterate any further.
                    # just return and we can simplify again
                    return True
        return False

    def simplify_formula(self, formula) -> bool:
        changed = False
        # flatten equalities
        if formula.is_eq():
            chld = formula.children()
            if len(chld) == 2 and chld[0].is_poly() and chld[1].is_poly():
                chld[1][0].change_sign()
                chld[0][0].add(chld[1][0])
                changed |= self._simplify_polynomial_formula(chld[0])
                formula.replace_with(
                    BVFormula(
                        ArithFormula.EQ,
                        None,
                        chld[0],
                        BVFormula.create(bv_const(0, chld[0][0].bitwidth())),
                    )
                )
            else:
                for c in formula.children():
                    changed |= self.simplify_formula(c)
        elif formula.is_poly():
            changed |= self._simplify_polynomial_formula(formula)
        else:
            for c in formula.children():
                changed |= self.simplify_formula(c)
        return changed


def simplify_polynomial_formula(formula, polynoms) -> None:
    simplifier = PolynomialSimplifier(*polynoms)
    while simplifier.simplify_formula(formula):
        pass


def rewrite_polynomials(expr_to: BVFormula, exprs_from):
    """
    Replace arithmetical operations with a fresh uninterpreted symbol.
    Return a mapping from new symbols to replaced expressions.
    Note: performs formula rewritings before the replacement.
    """
    exprs_from = exprs_from or []
    try:
        re = Tactic("elim-term-ite")(_rewrite_sext(_desimplify_ext(expr_to)))
        assert len(re) == 1, re
        expr_to = _desimplify_ext(simplify(mk_and(*re[0])))
        to_formula = BVFormula.create(expr_to)
        if to_formula is None:
            return expr_to
        simple_poly = []
        for e in exprs_from:
            e_formula = BVFormula.create(_desimplify_ext(e))
            if e_formula is None:
                continue
            if e_formula.is_eq():
                chlds = list(e_formula.children())
                if len(chlds) == 2 and chlds[0].is_poly() and chlds[1].is_poly():
                    P1 = chlds[0][0]
                    P2 = chlds[1][0]
                    P2.change_sign()
                    P1.add(P2)
                    simple_poly.append(P1)

        # print('--------')
        # for p in simple_poly:
        #    print('  > ASSUM', _desimplify_ext(simplify(p.expr())))
        # print('>ORIG', _desimplify_ext(simplify(to_formula.expr())))
        # print('--------')
        simplify_polynomial_formula(to_formula, simple_poly)
        #     print('>SIMPL', _desimplify_ext(simplify(to_formula.expr())))
        e = _desimplify_ext(simplify(to_formula.expr()))
        # print('   --   ')
        # print('>FINAL', e)
        # print('--------')
        return e
    except ValueError:
        return None


def get_eqs_from_ineqs(expr):
    ###
    # check for equalities from inequalities:
    # Not(1 + x <= c) && x <= c  ==> x=c

    # NOTE: requires expr in CNF
    clauses = set(expr.children())
    eqs = []
    for clause in clauses:
        # FIXME: Add greate-equal and check also for other patters
        # (a <= b & 1 + a > b), ...
        if is_app_of(clause, Z3_OP_SLEQ):
            chld = clause.children()
            nc = Not(1 + chld[0] <= chld[1])
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = Not(chld[0] + 1 <= chld[1])
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = chld[1] <= chld[0]
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = chld[0] >= chld[1]
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue

        if is_app_of(clause, Z3_OP_ULEQ):
            chld = clause.children()
            nc = Not(BVULE(1 + chld[0], chld[1]))
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = Not(BVULE(chld[0] + 1, chld[1]))
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = BVUGE(chld[0], chld[1])
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
            nc = BVULE(chld[1], chld[0])
            if nc in clauses:
                eqs.append((clause, nc, chld[0] == chld[1]))
                continue
    return eqs


def eqs_from_ineqs(expr):
    ###
    # check for equalities from inequalities:
    # Not(1 + x <= c) && x <= c  ==> x=c
    eqs = get_eqs_from_ineqs(expr)
    if eqs:
        clauses = set(expr.children())
        for c, nc, e in eqs:
            clauses.remove(c)
            clauses.remove(nc)
            clauses.add(e)
        return And(*clauses)
    return None


def replace_arith_ops(expr):
    """
    Replace arithmetical operations with a fresh uninterpreted symbol.
    Return a mapping from new symbols to replaced expressions.
    Note: performs formula rewritings before the replacement.
    """
    try:
        atoms = {}
        expr = mk_and(*Then("tseitin-cnf", With("simplify", som=True))(expr)[0])
        # assert len(expr_mod) == 1, expr_mod
        # expr = And(*expr_mod[0])
        _get_replacable(expr, atoms)
        subs = {}
        for e, num in atoms.items():
            if num < 1:
                continue
            subs[e] = BitVec(f"r_{hash(e)}", e.size())
        return substitute(expr, *subs.items()), subs
    except ValueError:
        return None, None


def _reduce_eq_bitwidth(expr, bw):
    if is_const(expr):
        return expr
    chld = expr.children()
    # Do we want to recurse also into operands of == and !=?
    if is_eq(expr):
        return BVExtract(bw - 1, 0, chld[0]) == BVExtract(bw - 1, 0, chld[1])
    elif is_not(expr):
        # do not dive into negations - negation of overapproximation
        # is underapproximation
        return expr
    else:
        red = [_reduce_eq_bitwidth(c, bw) for c in chld]
        if is_and(expr):
            return mk_and(*red)
        elif is_or(expr):
            return mk_or(*red)
        else:
            return expr.decl()(*red)


def reduce_eq_bitwidth(expr, bw):
    # return _reduce_eq_bitwidth(expr, bw, variables)
    try:
        # we need the expr in NNF
        expr_nnf = Tactic("nnf")(expr)
        assert len(expr_nnf) == 1, expr_nnf
        return _reduce_eq_bitwidth(mk_and(*expr_nnf[0]), bw)
    except ValueError:
        return None


def _rdw(expr, bw):
    oldbw = expr.size()
    if oldbw <= bw:
        return expr
    return BVZExt(oldbw - bw, BVExtract(bw - 1, 0, expr))


def _reduce_arith_bitwidth(expr, bw):
    if is_bv(expr):
        return _rdw(expr, bw)
    # oldbw = expr.size()
    # return BVExtract(bw-1, 0, expr) if oldbw > bw else expr
    else:
        red = (_reduce_arith_bitwidth(c, bw) for c in expr.children())
        if is_and(expr):
            return And(*red)
        elif is_or(expr):
            return Or(*red)
        return expr.decl()(*red)


def reduce_arith_bitwidth(expr, bw):
    # return _reduce_arith_bitwidth(expr, bw, variables)
    try:
        return _reduce_arith_bitwidth(expr, bw)
    except ValueError:
        return None
