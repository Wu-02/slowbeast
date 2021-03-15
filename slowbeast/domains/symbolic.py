from functools import reduce
from slowbeast.domains.value import Value
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import Type, IntType, BoolType, FloatType
from slowbeast.ir.instruction import FpOp
from slowbeast.util.debugging import FIXME

#FIXME move to its own file

def _distribute_two(c1, c2, mk_add, mk_mul):
    assert c1, c2
    if c1.is_add():
        if c2.is_add():
            return mk_add(*(mk_mul(a, b) for a in c1._children for b in c2._children))
        else:
            return mk_add(*(mk_mul(a, c2) for a in c1._children))
    elif c2.is_add():
        assert not c1.is_add()
        return mk_add(*(mk_mul(c1, a) for a in c2._children))
    return mk_mul(c1, c2)

class Monomial:
    """ Monomial (power product) """

    def __init__(self, *variables):
        self.vars = {v : e for v,e in variables if e != 0}

    def __getitem__(self, item):
        return self.vars.get(item)

    def copy(self):
        M = type(self)()
        M.vars = self.vars.copy()
        return M

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def degree(self):
        return sum(self.vars.values())

    def multiplied(self, *rhss):
        """ product of self and monomials in rhss. Returns a new object """

        V = self.vars
        newV = {}
        for m in rhss:
            assert isinstance(m, Monomial), m
            for v, e in m.vars.items():
                # increase exponent
                lv = V.get(v)
                exp = (lv or 0) + e
                if exp != 0:
                    newV[v] = exp
        # fill-in the rest of V
        for v, e in V.items():
            if newV.get(v) is None:
                newV[v] = e

        newMon = type(self)()
        newMon.vars = newV
        return newMon

    def divided(self, *rhss):
        newV = self.vars.copy()
        for m in rhss:
            assert isinstance(m, Monomial), m
            for v, e in m.vars.items():
                lv = newV.get(v)
                # decrease exponent
                if lv is None:
                    newV[v] = -e
                else:
                    # lv - e == 0
                    if lv == e:
                        newV.pop(v)
                    else:
                        newV[v] = lv - e
        newMon = type(self)()
        newMon.vars = newV
        return newMon

    def is_constant(self):
        return not self.vars

    def divides(self, rhs):
        RV = rhs.vars
        for v, e in self.vars.items():
            assert e != 0, self
            re = RV.get(v)
            if re is None:
                return False
            if re < e:
                return False
        return True

    def __eq__(self, rhs):
        return self.vars == rhs.vars

    def __hash__(self):
        #FIXME: we probably want some better hash
        return hash(sum(self.vars.values()))^hash(len(self.vars))

    def __repr__(self):
        V = self.vars
        if not V:
            return "[1]"
        return "[{0}]".format("·".join(f"{v}^{e}" if e != 1 else str(v) for v, e in V.items()))

class Polynomial:
    def __init__(self, *elems):
        # mapping from monomials to their coefficient
        self.monomials = {}
        self.add(*elems)

    def __getitem__(self, item):
        return self.monomials.get(item)

    def copy(self):
        P = type(self)()
        P.monomials = {m.copy() : c for m, c in self.monomials.items()}
        return P

    def clean_copy(self):
        return type(self)()

    def _create_coefficient(self, c, m):
        """
        Create a coefficient 'c' to monomial 'm'.
        This method can be overriden, e.g., to have the
        coefficients modulo something.
        """
        return c

    def _coefficient_is_zero(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == 0

    def _coefficient_is_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == 1

    def _coefficient_is_minus_one(self, c):
        """
        Check whether the coefficient is zero.
        This method can be overriden.
        """
        return c == -1

    def _simplify_coefficient(self, c):
        """
        Simplify the given coefficient.
        This method can be overriden.
        """
        return c

    def __iter__(self):
        return iter(self.monomials.items())

    def _add_monomial(self, r, coef=1):
        M = self.monomials
        cur = M.get(r)
        if cur is None:
            addcoef = self._create_coefficient(coef, r)
            if not self._coefficient_is_zero(addcoef):
                M[r] = addcoef
        else:
            assert not self._coefficient_is_zero(cur)
            newcoef = self._simplify_coefficient(cur + self._create_coefficient(coef, r))
            if self._coefficient_is_zero(newcoef):
                M.pop(r)
            else:
                M[r] = newcoef

    def add(self, *elems):
        M = self.monomials
        for r in elems:
            if isinstance(r, Monomial):
                self._add_monomial(r)
            elif isinstance(r, Polynomial):
                for rhsm, rhsc in r:
                    assert not self._coefficient_is_zero(rhsc), r
                    self._add_monomial(rhsm, rhsc)
            elif isinstance(r, tuple): # tuple of coef and monomial 
                self._add_monomial(r[1], r[0])
            else:
                raise NotImplementedError(f"Unhandled polynomial expression: {r}")

    def split(self, mons):
        """
        Put monomials from 'self' that match 'mons' to one polynom
        and the rest to other polynom
        """
        P1 = self.clean_copy()
        P2 = self.clean_copy()
        for m, c in self.monomials.items():
            if m in mons:
                P1.add((c, m))
            else:
                P2.add((c, m))
        return P1, P2

    def _mul_monomials(self, newP, lhsm, lhsc, rhsm, rhsc=None):
        newm = lhsm.multiplied(rhsm)
        newP[newm] = self._simplify_coefficient(lhsc * (self._create_coefficient(1, newm) if rhsc is None else rhsc))
 
    def mul(self, *m):
        newP = {}
        for lhsm, lhsc in self.monomials.items():
            assert not self._coefficient_is_zero(lhsc)
            for r in m:
                if isinstance(r, Monomial):
                    self._mul_monomials(newP, lhsm, lhsc, r)
                elif isinstance(r, Polynomial):
                    for rhsm, rhsc in r:
                        assert not self._coefficient_is_zero(rhsc), r
                        self._mul_monomials(newP, lhsm, lhsc, rhsm, rhsc)
                elif isinstance(r, tuple):
                    self._mul_monomials(newP, lhsm, lhsc, r[1], r[0])
                else:
                    raise NotImplementedError(f"Unhandled polynomial expression: {r}")
        self.monomials = newP

    def change_sign(self):
        newP = {}
        cc = self._create_coefficient
        sc = self._simplify_coefficient
        for m, c in self.monomials.items():
            newP[m] = sc(c*cc(-1, m))
        self.monomials = newP

    def max_degree(self):
        return max(self.monomials.keys())

    def has(self, m):
        return self.monomials.get(m) is not None

    def get_coef(self, m):
        return self.monomials.get(m)

    def coef_is_one(self, m):
        return self._coefficient_is_one(self.monomials.get(m))

    def coef_is_minus_one(self, m):
        return self._coefficient_is_minus_one(self.monomials.get(m))

    def is_normed(self, m):
        x = self.monomials.get(m)
        if x is None:
            return False
        return self._coefficient_is_one(x) or self._coefficient_is_minus_one(x)

    def max_degree_elems(self):
        md = -1
        elems = []
        for m, c in self.monomials.items():
            d = m.degree()
            if d > md:
                elems = [m]
                md = d
            elif d == md:
                elems.append(m)
        return elems

    def pop(self, *ms):
        for m in ms:
            assert isinstance(m, Monomial), m
            self.monomials.pop(m)

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def __repr__(self):
        return str(self.monomials)

    def __str__(self):
        return " + ".join(map(lambda x: f"{x[1]}·{x[0]}", self.monomials.items()))
    
class ArithFormula:
    """
    Helper class for representing formulas in LIA or BV theory.
    This class makes it easy to work with commutative expressions
    by merging the operands into sets (if the operation is commutative).
    """
    # commutative operations
    AND = 1
    OR  = 2
    EQ  = 6

    # non-commutative operations
    MT_NON_COMMUTATIVE=39
    MT_NON_ASSOCIATIVE=49
    # non-associative operations
    NOT = 51
    SLE = 52
    SLT = 53 
    ULT = 54 
    ULE = 55 
    SGE = 56
    SGT = 57 
    UGT = 58 
    UGE = 59 

    # variables, constants
    MT_VALUES = 100
    POLYNOM = 101

    def __init__(self, ty, value, *operands):
        assert value is None or ty > ArithFormula.MT_VALUES
        self._ty = ty
        self._value = value
        self._children = []

        # flatter the expression already here
        isac = ArithFormula.op_is_assoc_and_comm(ty)
        for o in operands:
            if isac and o._ty == ty:
                assert o.children(), o
                self.add_child(*o.children())
            elif ty == ArithFormula.ADD and o.value_equals(0):
                continue
            elif ty == ArithFormula.MUL and o.value_equals(1):
                continue
            else:
                self.add_child(o)


        if len(self._children) == 1 and ty != ArithFormula.NOT:
            elem = self._children.pop()
            self._value = elem._value
            self._ty = elem._ty


    def __getitem__(self, item):
        if self._children:
            assert item < len(self._children)
            return self._children[item]
        assert item == 0
        return self._value

    def add_child(self, *args):
        assert self._value is None, "Adding child to var/const"
        self._children.extend(args)

    def op_is_associative(op):
        return op <= ArithFormula.MT_NON_ASSOCIATIVE

    def op_is_commutative(op):
        return op <= ArithFormula.MT_NON_COMMUTATIVE

    def op_is_assoc_and_comm(op):
        return op <= ArithFormula.MT_NON_ASSOCIATIVE

    def __op_to_str(op):
        if op == ArithFormula.AND: return "∧"
        if op == ArithFormula.OR  : return "∨"
        if op == ArithFormula.NOT : return "not"
        if op == ArithFormula.EQ  : return "="
        if op == ArithFormula.SLE : return "≤"
        if op == ArithFormula.SLT : return "<" 
        if op == ArithFormula.ULT : return "<u" 
        if op == ArithFormula.ULE : return "≤u" 
        if op == ArithFormula.SGE : return "≥"
        if op == ArithFormula.SGT : return ">" 
        if op == ArithFormula.UGT : return ">u" 
        if op == ArithFormula.UGE : return "≥u" 
        return None

    def type(self):
        return self._ty

    def value(self):
        return self._value

    def value_equals(self):
        raise NotImplementedError("Must be overridden")

    def __iter__(self):
        return self._children.__iter__()

    def children(self):
        return self._children

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def expr(self):
        "Convert this object into expression for solver"
        raise NotImplementedError("Must be overridden")

    def is_eq(self): return self._ty == ArithFormula.EQ
    def is_not(self): return self._ty == ArithFormula.NOT
    def is_poly(self): return self._ty == ArithFormula.POLYNOM

    def substitute_inplace(self, *subs):
        """ Return True if the formula gets modified """
        changed = False
        newchldrn = []
        for op in self._children:
            changed |= op.substitute_inplace(*subs)

            for s, to in subs:
                # should substitute?
                if s == op:
                    if self._ty == to._ty and ArithFormula.op_is_assoc_and_comm(to._ty):
                        newchldrn.extend(to.children())
                    else:
                        newchldrn.append(to)
                    changed = True
                else:
                    newchldrn.append(op)
        self._children = newchldrn
        return changed

    def __eq__(self, rhs):
        return isinstance(rhs, ArithFormula) and\
                self._ty == rhs._ty and\
                self._value == rhs._value and\
                self._children == rhs._children

    # FIXME: not efficient
    def __hash__(self):
        v = self._value
        if v is not None: return hash(v)
        return hash(self._ty)# ^ reduce(lambda a, b: hash(a) ^ hash(b), self._children)

    def __repr__(self):
        ty = self._ty
        if ty == ArithFormula.NOT:
            assert len(self._children) == 1
            return f"¬({self._children[0]})"
        elif ty > ArithFormula.MT_VALUES:
            assert len(self._children) == 0
            return str(self._value)
        op = ArithFormula.__op_to_str(ty)
        assert op
        return "({0})".format(op.join(map(str, self._children)))


    def __str__(self):
        ty = self._ty
        if ty == ArithFormula.NOT:
            assert len(self._children) == 1, self._children
            if self._children[0]._ty == ArithFormula.EQ:
                return "({0})".format("≠".join(map(str, self._children[0]._children)))
            return f"¬({self._children[0]})"
        elif ty > ArithFormula.MT_VALUES:
            assert len(self._children) == 0
            return str(self._value)
        op = ArithFormula.__op_to_str(ty)
        assert op
        return "({0})".format(op.join(map(str, self._children)))


_use_z3 = True
if _use_z3:
    from z3 import (
        If,
        Or,
        And,
        Sum,
        Product,
        Xor,
        Not,
        Bool,
        BoolVal,
        BitVec,
        BitVecVal,
        BitVecSort,
        URem,
        SRem,
        UDiv,
        ULT as BVULT,
        ULE as BVULE,
        UGT as BVUGT,
        UGE as BVUGE,
        ZeroExt as BVZExt,
        SignExt as BVSExt,
        Extract as BVExtract,
        Concat as BVConcat,
        LShR as BVLShR,
    )
    from z3 import is_const, is_bv, is_bv_value, is_bool, is_and, is_or, is_not
    from z3 import is_mul, is_add, is_sub, is_div, is_eq, is_distinct
    from z3 import (
        is_app_of,
        Z3_OP_SLEQ,
        Z3_OP_SLT,
        Z3_OP_SGEQ,
        Z3_OP_SGT,
        Z3_OP_ULT,
        Z3_OP_ULEQ,
        Z3_OP_UGT,
        Z3_OP_UGEQ,
        Z3_OP_EQ,
        Z3_OP_BMUL,
        Z3_OP_BADD,
        Z3_OP_BSUB,
        Z3_OP_BUDIV,
        Z3_OP_BSDIV,
        Z3_OP_BUDIV_I,
        Z3_OP_BSDIV_I,
        Z3_OP_BUREM,
        Z3_OP_BUREM_I,
        Z3_OP_BSREM,
        Z3_OP_BSREM_I,
        Z3_OP_ZERO_EXT,
        Z3_OP_ITE,
        Z3_OP_SIGN_EXT,
        Z3_OP_CONCAT,
        Z3_OP_EXTRACT,
    )
    from z3 import is_true, is_false, simplify, substitute
    from z3 import Goal, Tactic, Then, With, Repeat, OrElse
    from z3 import (
        FP,
        Float32,
        Float64,
        Float128,
        FPVal,
        fpDiv,
        fpAbs,
        fpNeg,
        fpIsInf,
        fpIsNaN,
        fpIsSubnormal,
        fpIsZero,
        fpIsNegative,
        fpToFP,
        fpFPToFP,
        fpBVToFP,
        fpSignedToFP,
        fpUnsignedToFP,
        fpToIEEEBV,
        RNE,
        fpToUBV,
        fpToSBV,
        fpEQ,
        fpNEQ,
        fpGEQ,
        fpGT,
        fpLEQ,
        fpLT,
    )

    def trunc_fp(fexpr, bw):
        return simplify(fpFPToFP(RNE(), fexpr, get_fp_sort(bw)))

    def to_double(x):
        bw = x.bitwidth()
        if x.is_float() and bw == 64:
            return x._expr
        # we first must convert to float and then extend to double
        if x.is_float() and bw == 32:
            r = x._expr
        else:
            assert not x.is_float()
            # bitcast from IEEE
            r = simplify(fpToFP(x._expr, get_fp_sort(bw)))
        r = simplify(fpFPToFP(RNE(), r, Float64()))
        return r

    def to_bv(x):
        if x.is_float():
            r = simplify(fpToIEEEBV(x._expr))
            assert r.sort().size() == x.bitwidth(), f"{r.sort()}, {x.type()}"
            return r
        if x.is_bool():
            return boolToBV(x)
        return x.unwrap()

    def floatToUBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

    def floatToSBV(x, ty=None):
        if x.is_float():
            bw = ty.bitwidth() if ty else x.bitwidth()
            return simplify(fpToUBV(RNE(), x._expr, BitVecSort(bw)))

        return x.unwrap()

    def mk_or(*e):
        if len(e) == 1:
            return e[0]
        return Or(*e)

    def mk_and(*e):
        if len(e) == 1:
            return e[0]
        return And(*e)

    def eliminate_common_subexpr(expr):
        # XXX: not efficient, it is rather
        # to prettify expressions while debugging
        if is_and(expr):
            subexp = [eliminate_common_subexpr(c) for c in expr.children()]
            n = 0
            for idx in range(0, len(subexp)):
                c = subexp[idx]
                subs = [(s, BoolVal(True)) for (i, s) in enumerate(subexp) if i != n]
                subexp[idx] = simplify(substitute(c, *subs))
                n += 1
            return mk_and(*subexp)
        elif is_or(expr):
            return mk_or(*(eliminate_common_subexpr(c) for c in expr.children()))
        elif is_not(expr):
            return Not(*(eliminate_common_subexpr(c) for c in expr.children()))
        else:
            return expr

    def TRUE():
        return BoolVal(True)

    def FALSE():
        return BoolVal(False)

    def bv(name, bw):
        return BitVec(name, bw)

    def bv_const(v, bw):
        return BitVecVal(v, bw)

    def boolToBV(b):
        if not b.is_bool():
            return b.unwrap()
        return If(b.unwrap(), bv_const(1, 1), bv_const(0, 1))

    def castToFP(b):
        if b.is_float():
            return b.unwrap()
        return fpToFP(b.unwrap(), get_fp_sort(b.type().bitwidth()))

    def castToBool(b):
        if b.is_bool():
            return b.unwrap()
        return If(b.unwrap() != bv_const(0, b.bitwidth()), TRUE(), FALSE())

    def bv_size(bw):
        return bw.sort().size()


    def _expr_op_to_formula_op(expr):
        if is_and(expr): return ArithFormula.AND
        if is_or(expr): return ArithFormula.OR
        if is_not(expr): return ArithFormula.NOT

        if is_eq(expr): return ArithFormula.EQ
        if is_app_of(expr, Z3_OP_SLEQ): return ArithFormula.SLE
        if is_app_of(expr, Z3_OP_SLT): return ArithFormula.SLT
        if is_app_of(expr, Z3_OP_ULEQ): return ArithFormula.ULE
        if is_app_of(expr, Z3_OP_ULT): return ArithFormula.ULT
        if is_app_of(expr, Z3_OP_SGEQ): return ArithFormula.SGE
        if is_app_of(expr, Z3_OP_SGT): return ArithFormula.SGT
        if is_app_of(expr, Z3_OP_UGEQ): return ArithFormula.UGE
        if is_app_of(expr, Z3_OP_UGT): return ArithFormula.UGT

        #raise NotImplementedError(f"Unhandled operation: {expr}")
        return None

    class BVMonomial(Monomial):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """
        def __init__(self, *variabl):
            super().__init__(*variabl)

        def create(expr):
            raise NotImplementedError("Must be overridden")

        def expr(self):
            " Transform to Z3 expressions "
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
        def __init__(self, bw, *elems):
            self._bw = bw #bitwidth
            super().__init__(*elems)

        def bitwidth(self):
            return self._bw

        def copy(self):
            P = type(self)(self._bw)
            P.monomials = {m.copy() : c for m, c in self.monomials.items()}
            return P

        def clean_copy(self):
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

        def create(expr):
            bw = expr.size()
            if is_app_of(expr, Z3_OP_BADD):
                return BVPolynomial(bw, *(BVPolynomial.create(e) for e in expr.children()))
            elif is_app_of(expr, Z3_OP_BMUL):
                pols = [BVPolynomial.create(e) for e in expr.children()]
                P = pols[0]
                for i in range(1, len(pols)):
                    P.mul(pols[i])
                return P
            elif is_app_of(expr, Z3_OP_CONCAT) or\
                    is_app_of(expr, Z3_OP_SIGN_EXT) or\
                    is_app_of(expr, Z3_OP_ZERO_EXT):
                # TODO: check that these operations are applied to const?
                return BVPolynomial(bw, BVMonomial((expr, 1)))
            elif is_app_of(expr, Z3_OP_BUREM) or\
                    is_app_of(expr, Z3_OP_BUREM_I) or\
                    is_app_of(expr, Z3_OP_BSREM) or\
                    is_app_of(expr, Z3_OP_BSREM_I) or\
                    is_app_of(expr, Z3_OP_BUDIV) or\
                    is_app_of(expr, Z3_OP_BSDIV) or\
                    is_app_of(expr, Z3_OP_BUDIV_I) or\
                    is_app_of(expr, Z3_OP_BSDIV_I):
                # TODO: check that these operations are applied to const?
                return BVPolynomial(bw, BVMonomial((expr, 1)))
            elif is_const(expr):
                if is_bv_value(expr):
                    return BVPolynomial(bw, (expr, BVMonomial()))
                return BVPolynomial(bw, BVMonomial((expr, 1)))
            raise NotImplementedError(f"Unhandeld expression: {expr}")

        def expr(self):
            " Transform to Z3 expressions "
            M = self.monomials
            if not M:
                return bv_const(0, self._bw)

            it = iter(M.items())
            m, c = next(it)
            mexpr = m.expr()
            expr = c if mexpr is None else c*mexpr
            for m, c in it:
                mexpr = m.expr()
                expr += c if mexpr is None else c*mexpr
            return simplify(expr)

    class BVFormula(ArithFormula):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """
        def __init__(self, ty, *operands):
            super().__init__(ty, *operands)

        def create(expr):
            chlds = expr.children()
            op = _expr_op_to_formula_op(expr)
            if chlds:
                if op is None:
                    # it is a polynomial
                    return BVFormula(ArithFormula.POLYNOM,
                                     BVPolynomial.create(expr))
                isac = ArithFormula.op_is_assoc_and_comm(op)
                formula = BVFormula(op, None)
                for c in chlds:
                    if isac and op == _expr_op_to_formula_op(c):
                        formula.add_child(*(BVFormula.create(c).children()))
                    else:
                        formula.add_child(BVFormula.create(c))
                return formula
               #return BVFormula(_expr_op_to_formula_op(expr), None,
               #                 *(BVFormula.create(c) for c in chlds))
            return BVFormula(ArithFormula.POLYNOM,
                             BVPolynomial.create(expr))

        def value_equals(self, x):
            v = self._value
            if v is None:
                return False
            return is_bv_value(v) and v.as_long() == x

        def expr(self):
            "Convert this object into expression for solver"
            ty = self._ty
            if ty == ArithFormula.POLYNOM:
                return self._value.expr()
            if ty == ArithFormula.AND:
                return mk_and(*(c.expr() for c in self._children))
            if ty == ArithFormula.OR:
                return mk_or(*(c.expr() for c in self._children))
            if ty == ArithFormula.NOT:
                assert len(self._children) == 1
                return Not(self._children[0].expr())

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

    def subexpressions(expr):
        children = expr.children()
        for c in children:
            yield from subexpressions(c)
        yield expr

    def is_lit(e):
        return is_const(e) or\
                ((is_app_of(e, Z3_OP_ZERO_EXT) or\
                  is_app_of(e, Z3_OP_SIGN_EXT) or\
                  is_app_of(e, Z3_OP_CONCAT) or\
                  is_app_of(e, Z3_OP_EXTRACT)) and is_lit(e.children()[0]))

    def _is_const_mul(expr):
        chld = expr.children()
        return is_app_of(expr, Z3_OP_BMUL) and is_lit(chld[0]) and is_lit(chld[1])

    def _get_replacable(expr, atoms):
        chld = expr.children()
        if _is_const_mul(expr):
            v = atoms.setdefault(expr, 0)
            atoms[expr] = v + 1
            return
        for c in chld:
           _get_replacable(c, atoms)

    def _desimplify_ext(expr):
        " replace concat with singext if possible -- due to debugging "
        if is_const(expr):
            return expr
        chld = expr.children()
        # Do we want to recurse also into operands of == and !=?
        if is_app_of(expr, Z3_OP_CONCAT):
            c0 = chld[0]
            if is_app_of(c0, Z3_OP_EXTRACT):
                params = c0.params()
                if params[0] == params[1] == (chld[-1].size() - 1) and c0.children()[0] == chld[-1]:
                    if all(map(lambda e: e == c0, chld[1:-1])):
                        return BVSExt(expr.size() - chld[-1].size(), chld[-1])
            return expr
        else:
            red = [_desimplify_ext(c) for c in chld]
            if is_and(expr): return mk_and(*red)
            elif is_or(expr): return mk_or(*red)
            elif is_app_of(expr, Z3_OP_CONCAT): return BVConcat(*red)
            else:
                if len(red) > 2:
                    e = expr.decl()(red[0], red[1])
                    for i in range(2, len(red)):
                        e = expr.decl()(e, red[i])
                    return e
                else:
                    return expr.decl()(*red)

    def _rewrite_sext(expr):
        " replace sext(x + c) with sext(x) + c if possible "
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
                            return If(x != 2**(bw-1)-1,
                                      #BVSExt(ebw - bw, x) + BVZExt(ebw - bw, c),
                                      #expr)
                                      BVSExt(ebw - bw, x) + bv_const(1, ebw),
                                      simplify(BVSExt(ebw - bw,
                                                      bv_const(2**bw-1, bw) + 1))
                                        )
                        # expr = sext(x + (-1))
                        elif simplify(c == -1).__bool__():
                            return If(x != 2**(bw-1),
                                      #BVSExt(ebw - bw, x) + BVSExt(ebw - bw, c),
                                      #expr)
                                      BVSExt(ebw - bw, x) + bv_const(-1, ebw),
                                      simplify(BVSExt(ebw - bw,
                                                      bv_const(2**bw-1, bw) -
                                                      1))
                                      )
                        # FIXME: do this for generic values
            return expr
        else:
            red = [_rewrite_sext(c) for c in chld]
            if is_and(expr): return mk_and(*red)
            elif is_or(expr): return mk_or(*red)
            elif is_app_of(expr, Z3_OP_CONCAT): return BVConcat(*red)
            else:
                if len(red) > 2:
                    e = expr.decl()(red[0], red[1])
                    for i in range(2, len(red)):
                        e = expr.decl()(e, red[i])
                    return e
                else:
                    return expr.decl()(*red)

    def _get_common_monomials(P1, P2, same_coef=False):
        monomials = []
        for p1m, c1 in P1.monomials.items():
            c2 = P2.get_coef(p1m)
            if c2 is None:
                continue
            if not same_coef or c1 == c2:
                monomials.append(p1m)
        return monomials

    def _simplify_polynomial_formula(formula, polynoms):
        assert formula.is_poly(), formula
        P = formula[0]
        for p in polynoms:
            me = p.max_degree_elems()
            if len(me) != 1:
                # FIXME: we should keep track of polynomials that we substitued
                # to not to get into a cycle
                common = _get_common_monomials(p, P, same_coef=True)
                if common and all(map(lambda c: c in common, me)):
                    p1, p2 = p.split(common)
                    p1.change_sign()
                    P.add(p1)
                    P.add(p2)
                    continue
                mP = P.copy()
                mP.change_sign()
                common = _get_common_monomials(p, mP, same_coef=True)
                if common and all(map(lambda c: c in common, me)):
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
               #mc = P.get_coef(monomial)
               #mec = p.get_coef(mme)
                if not P.is_normed(monomial):
                    continue # FOR NOW
                if mme.divides(monomial):
                    # FIXME: multiply with the coefficient!
                    r = BVPolynomial(P.bitwidth(), monomial.divided(mme))
                    #print('-- REPLACING --')
                    p1, p2 = p.split([mme])
                   #print('  < ', p1)
                   #print('  > ', p2)
                   #print('  in ', monomial)
                    p2.change_sign()
                    r.mul(p2) # do the substitution
                    P.pop(monomial)
                    P.add(r)
                    # we changed the polynomial, we cannot iterate any further.
                    # just return and we can simplify again
                    return True
        return False

    def simplify_polynomial_formula(formula, polynoms):
        changed = False
        for c in formula.children():
            changed |= simplify_polynomial_formula(c, polynoms)
        if formula.is_poly():
            changed |= _simplify_polynomial_formula(formula, polynoms)
        return changed

    def replace_common_subexprs(expr_to, exprs_from):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        if not exprs_from:
            return expr_to

        try:
            re = Tactic("elim-term-ite")(_rewrite_sext(_desimplify_ext(expr_to)))
            assert len(re) == 1, re
            expr_to = _desimplify_ext(simplify(mk_and(*re[0])))
            to_formula = BVFormula.create(expr_to)
            simple_poly = []
            for e in exprs_from:
                e_formula = BVFormula.create(_desimplify_ext(e))
                if e_formula.is_eq():
                    chlds = list(e_formula.children())
                    if len(chlds) == 2 and chlds[0].is_poly() and chlds[1].is_poly():
                        P1 = chlds[0][0]
                        P2 = chlds[1][0]
                        P2.change_sign()
                        P1.add(P2)
                        if simple_poly:
                            simple_poly.append(P1.copy())
                            P = BVFormula(ArithFormula.POLYNOM, P1)
                            while simplify_polynomial_formula(P, simple_poly):
                                simple_poly.append(P[0])
                        else:
                            simple_poly.append(P1)

            if not simple_poly:
                return expr_to

           #print('--------')
           #for p in simple_poly:
           #    print('  > ASSUM', _desimplify_ext(simplify(p.expr())))
           #print('>ORIG', _desimplify_ext(simplify(to_formula.expr())))
           #print('--------')
            while simplify_polynomial_formula(to_formula, simple_poly):
           #     print('>SIMPL', _desimplify_ext(simplify(to_formula.expr())))
                pass
            e = _desimplify_ext(simplify(to_formula.expr()))
           #print('   --   ')
           #print('>FINAL', e)
           #print('--------')
            return e
        except ValueError:
            return None

    def replace_arith_ops(expr):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        try:
            atoms = {}
            expr = mk_and(*Then("tseitin-cnf",
                             With("simplify", som=True))(expr)[0])
           #assert len(expr_mod) == 1, expr_mod
           #expr = And(*expr_mod[0])
            _get_replacable(expr, atoms)
            subs = {}
            for e, num in atoms.items():
                if num < 1: continue
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
            return (BVExtract(bw-1, 0, chld[0]) ==\
                    BVExtract(bw-1, 0, chld[1])) 
        elif is_not(expr):
            # do not dive into negations - negation of overapproximation
            # is underapproximation
            return expr
        else:
            red = (_reduce_eq_bitwidth(c, bw) for c in chld)
            if is_and(expr): return mk_and(*red)
            elif is_or(expr): return mk_or(*red)
           #elif is_add(expr): return Sum(*red)
           #elif is_mul(expr): return Product(*red)
            else: return expr.decl()(*red)


    def reduce_eq_bitwidth(expr, bw):
        #return _reduce_eq_bitwidth(expr, bw, variables)
        try:
            # we need the expr in NNF
            expr_nnf = Tactic("nnf")(expr)
            assert len(expr_nnf) == 1, expr_nnf
            return _reduce_eq_bitwidth(mk_and(*expr_nnf[0]), bw)
        except ValueError:
            return None

    def to_cnf(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Tactic("tseitin-cnf")
        goal = t(g)
        assert len(goal) == 1
        return goal[0]

    def to_nnf(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Tactic("nnf")
        goal = t(g)
        assert len(goal) == 1
        return goal[0]

    def rewrite_simplify(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Then(With('simplify', arith_lhs=True, som=True),
                 Tactic('propagate-ineqs'),
                 Tactic('normalize-bounds'),
                 Tactic('propagate-values'),
                 Tactic('simplify'))
        return t(g)

    def split_clauses(*exprs):
        g = Goal()
        g.add(*exprs)
        t = Repeat(OrElse(Tactic('split-clause'),
                          Tactic('skip')))
        return t(g)

    def solver_to_sb_type(s):
        if is_bv(s):
            return IntType(s.sort().size())
        assert is_bool(s), f"Unhandled expression: {s}"
        return BoolType()

    def get_fp_sort(bw):
        if bw == 32:
            return Float32()
        if bw == 64:
            return Float64()
        elif bw == 128:
            return Float128()
        raise NotImplementedError("Invalid FP type")


else:
    from pysmt.shortcuts import Or, And, Not, Symbol, BV, TRUE, FALSE
    from pysmt.shortcuts import BVULT, BVULE, BVUGT, BVUGE
    from pysmt.typing import BVType

    def bv(name, bw):
        return Symbol(name, BVType(bw))

    def bv_const(v, bw):
        return BV(v, bw)


def dom_is_symbolic(v):
    return v.KIND == 2


class Expr(Value):
    """
    Wrapper around a formula that carries
    metadata like a type (and hash in the future, etc.)
    """

    # FIXME: get rid of the magic constant
    KIND = 2

    __slots__ = "_expr"

    def __init__(self, e, t):
        assert not isinstance(e, int), e
        assert isinstance(t, Type), t
        Value.__init__(self, t)
        self._expr = e

    def unwrap(self):
        return self._expr

    def is_nondet_load(self):
        return False

    def is_nondet_instr_result(self):
        return False

    def is_future(self):
        return False

    def name(self):
        return str(self._expr)

    def is_concrete(self):
        return False

    def as_value(self):
        return str(self)

    def subexpressions(self):
        """ Traverse the expression and return its all subexpressions """
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in subexpressions(self.unwrap())
        )

    def children(self):
        """
        Get the children (1st-level subexpressions) of this expression.
        E.g. for And(a, b) this method returns [a, b].
        """
        return (
            ConcreteVal(s.as_long(), solver_to_sb_type(s))
            if is_bv_value(s)
            else Expr(s, solver_to_sb_type(s))
            for s in self.unwrap().children()
        )

    def to_cnf(self):
        """
        Get the expression in CNF form.
        """
        return Expr(And(*to_cnf(self.unwrap())), self.type())

    def rewrite_and_simplify(self):
        """
        Get the expression in CNF form.
        """
        return Expr(mk_or(*(And(*c) for c in rewrite_simplify(self._expr))), self.type())

    def split_clauses(self):
        """
        Get the expression in CNF form.
        """
        return Expr(mk_or(*(And(*c) for c in split_clauses(self._expr))), self.type())

    def reduce_eq_bitwidth(self, bw):
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

    def replace_common_subexprs(self, from_exprs):
        expr = replace_common_subexprs(self.unwrap(), map(lambda x: x.unwrap(), from_exprs))
        if expr is None:
            return None
        return Expr(expr, self.type())



    def replace_arith_ops(self):
        """
        Reduce the maximal bitwith of arithmetic operations to 'bw'
        (return new expression). The resulting expression is
        overapproximation of the original one.
        \return None on failure (e.g., unsupported expression)
        """
        expr, subs = replace_arith_ops(self.unwrap())
        if expr is None:
            return None, None
        return Expr(expr, self.type()),\
               {Expr(k, solver_to_sb_type(k)) : Expr(v, solver_to_sb_type(v)) for k, v in subs.items()}

    def isAnd(self):
        return is_and(self.unwrap())

    def isOr(self):
        return is_or(self.unwrap())

    def isNot(self):
        return is_not(self.unwrap())

    def isEq(self):
        return is_app_of(self._expr, Z3_OP_EQ)

    def isLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ) or is_app_of(self._expr, Z3_OP_ULEQ)

    def isGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ) or is_app_of(self._expr, Z3_OP_UGEQ)

    def isLt(self):
        return is_app_of(self._expr, Z3_OP_SLT) or is_app_of(self._expr, Z3_OP_ULT)

    def isGt(self):
        return is_app_of(self._expr, Z3_OP_SGT) or is_app_of(self._expr, Z3_OP_UGT)

    def isSLe(self):
        return is_app_of(self._expr, Z3_OP_SLEQ)

    def isSGe(self):
        return is_app_of(self._expr, Z3_OP_SGEQ)

    def isSLt(self):
        return is_app_of(self._expr, Z3_OP_SLT)

    def isSGt(self):
        return is_app_of(self._expr, Z3_OP_SGT)

    def isULe(self):
        return is_app_of(self._expr, Z3_OP_ULEQ)

    def isUGe(self):
        return is_app_of(self._expr, Z3_OP_UGEQ)

    def isULt(self):
        return is_app_of(self._expr, Z3_OP_ULT)

    def isUGt(self):
        return is_app_of(self._expr, Z3_OP_UGT)

    def isMul(self):
        return is_app_of(self._expr, Z3_OP_BMUL)# or is_app_of(self._expr, Z3_OP_MUL)

    def __hash__(self):
        return self._expr.__hash__()

    def __eq__(self, rhs):
        return self._expr == rhs._expr

    def __repr__(self):
        return "<{0}:{1}>".format(self._expr, self.type())


class NondetLoad(Expr):
    __slots__ = "load", "alloc"

    def __init__(self, e, t, load, alloc):
        super().__init__(e, t)
        self.load = load
        self.alloc = alloc

    def is_nondet_load(self):
        return True

    def fromExpr(expr, load, alloc):
        assert isinstance(expr, Expr)
        return NondetLoad(expr.unwrap(), expr.type(), load, alloc)

    def rhs_repr(self):
        return Expr.__repr__(self)

    def __repr__(self):
        return f"L({self.alloc.as_value()})={Expr.__repr__(self)}"


class NondetInstrResult(Expr):
    """ Expression representing a result of instruction that is unknown - non-deterministic """

    __slots__ = "_instr"

    def __init__(self, e, t, instr):
        super().__init__(e, t)
        self._instr = instr

    def is_nondet_instr_result(self):
        return True

    def instruction(self):
        return self._instr

    def fromExpr(expr, instr):
        assert isinstance(expr, Expr)
        return NondetInstrResult(expr.unwrap(), expr.type(), instr)

    def __repr__(self):
        return f"{self._instr.as_value()}={Expr.__repr__(self)}"


class Future(Expr):
    """
    Represents a value of non-executed operation (instruction)
    (that is going to be executed as a feedback to the developement of the search
    """

    __slots__ = "_instr", "_state"

    def __init__(self, e, t, instr, state):
        super().__init__(e, t)
        # to which instr we assigned the nondet value
        self._instr = instr
        # stored state
        self._state = state

    def is_future(self):
        return True

    def state(self):
        return self._state

    def from_expr(expr, instr, state):
        assert isinstance(expr, Expr)
        return Future(expr.unwrap(), expr.type(), instr)

    def __repr__(self):
        return f"future({self._instr.as_value()})={super().__repr__()}"


def zext_expr(a, bw):
    return BVZExt(bw - a.bitwidth(), boolToBV(a))


def sext_expr(a, bw):
    return BVSExt(bw - a.bitwidth(), boolToBV(a))


class BVSymbolicDomain:
    """
    Takes care of handling symbolic computations
    (creating expressions only).
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            if a.KIND != 2:
                return False
        return True

    def lift(v):
        assert isinstance(v, Value), "Invalid value for lifting: {0}".format(v)
        if isinstance(v, Expr):
            return v

        if v.is_concrete():
            if v.is_bool():
                return Expr(BoolVal(v.value()), BoolType())
            ty = v.type()
            if v.is_float():
                return Expr(FPVal(v.value(), get_fp_sort(ty.bitwidth())), ty)
            return Expr(bv_const(v.value(), ty.bitwidth()), ty)

        raise NotImplementedError("Invalid value for lifting: {0}".format(v))

    def simplify(expr):
        return Expr(
            simplify(expr.unwrap(), arith_ineq_lhs=True, sort_sums=True), expr.type()
        )

    def substitute(expr, *what):
        return Expr(
            substitute(expr.unwrap(), *((a.unwrap(), b.unwrap()) for (a, b) in what)),
            expr.type(),
        )

    def pythonConstant(expr):
        """Take a symbolic constant and get a python constant for it.
        Return None if the given expression is not a constant number
        or boolean
        """
        val = expr.unwrap()
        if is_bv_value(val):
            return val.as_long()
        elif is_true(val):
            return True
        elif is_false(val):
            return False

        return None

    def Constant(c, ty):
        bw = ty.bitwidth()
        if ty.is_float():
            return Expr(FPVal(c, fps=get_fp_sort(bw)), ty)
        elif ty.is_int():
            return Expr(bv_const(c, bw), ty)
        else:
            raise NotImplementedError(f"Invalid type: {ty}")

    ##
    # variables
    def Var(name, ty):
        if ty.is_float():
            return Expr(FP(name, get_fp_sort(ty.bitwidth())), ty)
        elif ty.is_bool():
            return Expr(Bool(name), ty)
        else:
            assert ty.is_int() or ty.is_pointer(), ty
            return Expr(bv(name, ty.bitwidth()), ty)

    def BVVar(name, bw):
        return Expr(bv(name, bw), IntType(bw))

    def Bool(name):
        return Expr(Bool(name), BoolType())

    def Int1(name, ty):
        return BVSymbolicDomain.BVVar(name, 1)

    def Int8(name):
        return BVSymbolicDomain.BVVar(name, 8)

    def Int16(name):
        return BVSymbolicDomain.BVVar(name, 16)

    def Int32(name):
        return BVSymbolicDomain.BVVar(name, 32)

    def Int64(name):
        return BVSymbolicDomain.BVVar(name, 64)

    ##
    # Logic operators
    def conjunction(*args):
        """
        Logical and that allows to put into conjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(And(*map(lambda x: x.unwrap(), args)), BoolType())

    def disjunction(*args):
        """
        Logical and that allows to put into disjunction more
        than two formulas at once (just simplifies the formulas for
        reading and simplifications), it is not needed, really.
        """
        assert BVSymbolicDomain.belongto(*args)
        assert all(map(lambda x: x.is_bool(), args))
        return Expr(Or(*map(lambda x: x.unwrap(), args)), BoolType())

    def Ite(c, a, b):
        assert BVSymbolicDomain.belongto(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return Expr(If(c.unwrap(), a.unwrap(), b.unwrap()), a.type())

    def And(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(And(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) & to_bv(b), IntType(a.bitwidth()))

    def Or(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Or(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) | to_bv(b), IntType(a.bitwidth()))

    def Xor(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool() and b.is_bool():
            return Expr(Xor(a.unwrap(), b.unwrap()), BoolType())
        else:
            # bitwise and
            return Expr(to_bv(a) ^ to_bv(b), IntType(a.bitwidth()))

    def Not(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_bool():
            return Expr(Not(a.unwrap()), BoolType())
        else:
            return Expr(~to_bv(a), IntType(a.bitwidth()))

    def ZExt(a, b):
        assert BVSymbolicDomain.belongto(a)
        assert b.is_concrete()
        bw = b.value()
        assert a.bitwidth() <= bw, "Invalid zext argument"
        # BVZExt takes only 'increase' of the bitwidth
        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVZExt(bw - a.bitwidth(), ae), IntType(bw))

    def SExt(a, b):
        assert BVSymbolicDomain.belongto(a), a
        assert b.is_concrete(), b
        assert b.is_int(), b
        bw = b.value()
        assert a.bitwidth() <= bw, f"Invalid sext argument: {a} to {bw} bits"

        ae = to_bv(a) if a.is_float() else boolToBV(a)
        return Expr(BVSExt(bw - a.bitwidth(), ae), IntType(bw))

    def BitCast(a: Value, ty: Type):
        """ Static cast """
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float() and a.is_bytes():
            # from IEEE bitvector
            expr = fpToFP(a._expr, get_fp_sort(tybw))
            return Expr(expr, ty)
        if ty.is_float():
            if a.is_int():
                # from IEEE bitvector
                expr = fpToFP(a._expr, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
        elif a.is_float() and ty.is_int():
            ae = fpToIEEEBV(a._expr)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), IntType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    def Cast(a: Value, ty: Type, signed: bool = True):
        """ Reinterpret cast """
        assert BVSymbolicDomain.belongto(a)
        tybw = ty.bitwidth()
        if ty.is_float():
            if a.is_int():
                abw = a.bitwidth()
                if signed:  # from signed bitvector
                    expr = fpSignedToFP(RNE(), a._expr, get_fp_sort(tybw))
                else:
                    expr = fpUnsignedToFP(RNE(), a._expr, get_fp_sort(tybw))
                    # from IEEE bitvector
                    # expr = fpToFP(a._expr, get_fp_sort(tybw))
                # expr = fpToFP(a._expr, get_fp_sort(tybw))
                return Expr(expr, ty)
            elif a.is_float():
                return Expr(fpFPToFP(RNE(), a.unwrap(), get_fp_sort(tybw)), ty)
            if a.is_bytes():
                # from IEEE bitvector
                expr = fpToFP(a._expr, get_fp_sort(a.bitwidth()))
                expr = fpFPToFP(RNE(), expr, get_fp_sort(tybw))
                return Expr(expr, ty)
        elif a.is_float() and ty.is_int():
            if signed:
                ae = floatToSBV(a, ty)
            else:
                ae = floatToUBV(a, ty)
            # ae = fpToIEEEBV(a._expr)
            return Expr(ae, ty)
        elif a.is_bool() and ty.is_int():
            return Expr(
                If(a.unwrap(), bv_const(1, tybw), bv_const(0, tybw)), IntType(tybw)
            )
        elif a.is_int() and ty.is_bool():
            return Expr(
                If((a.unwrap() != bv_const(0, a.bitwidth())), TRUE(), FALSE()),
                BoolType(),
            )
        return None  # unsupported conversion

    def Extract(a, start, end):
        assert BVSymbolicDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        return Expr(
            BVExtract(end.value(), start.value(), a.unwrap()),
            IntType(end.value() - start.value() + 1),
        )

    def Concat(*args):
        l = len(args)
        assert l > 0, args
        assert BVSymbolicDomain.belongto(*args), args
        if l == 1:
            return args[0]
        return Expr(
            BVConcat(*(e.unwrap() for e in args)),
            IntType(sum(e.bitwidth() for e in args)),
        )

    def Shl(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) << b.unwrap(), IntType(a.bitwidth()))

    def AShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(to_bv(a) >> b.unwrap(), IntType(a.bitwidth()))

    def LShr(a, b):
        assert BVSymbolicDomain.belongto(a, b)
        assert b.is_int(), b
        return Expr(BVLShR(to_bv(a), b.unwrap()), IntType(a.bitwidth()))

    def getTrue():
        return Expr(TRUE(), BoolType())

    def getFalse():
        return Expr(FALSE(), BoolType())

    ##
    # Relational operators

    def Le(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        # we need this explicit float cast for the cases when a or b are
        # nondet loads (in which case they are bitvectors)
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) <= to_bv(b), BoolType())

    def Lt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpLT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVULT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) < to_bv(b), BoolType())

    def Ge(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGE(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) >= to_bv(b), BoolType())

    def Gt(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpGT(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        if unsigned:
            return Expr(BVUGT(to_bv(a), to_bv(b)), BoolType())
        return Expr(to_bv(a) > to_bv(b), BoolType())

    def Eq(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        return Expr(to_bv(a) == to_bv(b), BoolType())

    def Ne(a, b, unsigned=False, floats=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            a, b = castToFP(a), castToFP(b)
            expr = fpNEQ(a, b)
            if not unsigned:
                expr = And(expr, Not(fpIsNaN(a)), Not(fpIsNaN(b)))
            return Expr(expr, BoolType())
        return Expr(to_bv(a) != to_bv(b), BoolType())

    ##
    # Arithmetic operations
    def Add(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} + {b}"
        bw = a.bitwidth()
        if isfloat:
            # the operations on CPU work on doubles( well, 80-bits...)
            # and then truncate to float if needed
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae + be, bw), FloatType(bw))
        return Expr(to_bv(a) + to_bv(b), IntType(bw))

    def Sub(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} - {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae - be, bw), FloatType(bw))
        return Expr(to_bv(a) - to_bv(b), IntType(bw))

    def Mul(a, b, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} * {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(ae * be, bw), FloatType(bw))
        return Expr(to_bv(a) * to_bv(b), IntType(bw))

    def Div(a, b, unsigned=False, isfloat=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a} / {b}"
        bw = a.bitwidth()
        if isfloat:
            ae = to_double(a)
            be = to_double(b)
            return Expr(trunc_fp(fpDiv(RNE(), ae, be), bw), FloatType(bw))
        if unsigned:
            return Expr(UDiv(to_bv(a), to_bv(b)), IntType(bw))
        return Expr(to_bv(a) / to_bv(b), IntType(bw))

    def Rem(a, b, unsigned=False):
        assert BVSymbolicDomain.belongto(a, b)
        assert a.type() == b.type(), "Operation on invalid types: {0} != {1}".format(
            a.type(), b.type()
        )
        result_ty = a.type()
        if unsigned:
            return Expr(URem(a.unwrap(), b.unwrap()), result_ty)
        return Expr(SRem(a.unwrap(), b.unwrap()), result_ty)

    def Abs(a):
        assert BVSymbolicDomain.belongto(a)
        if a.is_float():
            return Expr(fpAbs(a.unwrap()), a.type())
        expr = a.unwrap()
        return Expr(If(expr < 0, -expr, expr), a.type())

    def Neg(a, isfloat):
        """ Return the negated number """
        assert BVSymbolicDomain.belongto(a)
        bw = a.bitwidth()
        if isfloat:
            return Expr(trunc_fp(fpNeg(to_double(a)), bw), FloatType(bw))
        expr = a.unwrap()
        return Expr(-expr, a.type())

    def FpOp(op, val):
        assert BVSymbolicDomain.belongto(val)
        # FIXME: do not use the enum from instruction
        assert val.is_float()

        if op == FpOp.IS_INF:
            return Expr(fpIsInf(val.unwrap()), BoolType())
        if op == FpOp.IS_NAN:
            return Expr(fpIsNaN(val.unwrap()), BoolType())
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.unwrap()
            expr = If(
                fpIsNaN(v),
                bv_const(0, 32),
                If(
                    fpIsInf(v),
                    bv_const(1, 32),
                    If(
                        fpIsZero(v),
                        bv_const(2, 32),
                        If(fpIsSubnormal(v), bv_const(3, 32), bv_const(4, 32)),
                    ),
                ),
            )
            return Expr(expr, IntType(32))
            if op == FpOp.SIGNBIT:
                return Expr(
                    If(fpIsNegative(bv_const(1, 32), bv_const(0, 32))), IntType(32)
                )

        return None


# The default symbolic domain are bitvectors
SymbolicDomain = BVSymbolicDomain
