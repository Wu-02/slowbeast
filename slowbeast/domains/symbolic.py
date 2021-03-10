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
    def __init__(self, coef, *variables):
        assert coef != 0
        self.coef = coef
        self.vars = {v : e for v,e in variables if e != 0}

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def _is_same(self, rhs):
        RV = rhs.vars
        for v, e in self.vars:
            assert e != 0, self.vars
            re = RV.get(v)
            if re is None or re != e:
                return False
        return False

    def is_same(self, rhs):
        return self._is_same(rhs) and rhs._is_same(self)

    def mul(self, *rhss):
        for m in rhss:
            assert isinstance(m, Monomial), m
            coef = self.coef
            V = self.vars
            for v, e in m.vars.items():
                # increase exponent
                lv = V.setdefault(v, 0)
                if lv + e != 0:
                    V[v] = lv + e
                else:
                    V.remove(v)
                coef *= m.coef

    def __repr__(self):
        coef = self.coef
        r = "" if coef == 1 else "-" if coef == -1 else str(coef)
        for v, e in self.vars.items():
            r += f"{v}^{e}" if e != 1 else str(v)
        return r

class Polynomial:
    def __init__(self, *monomials):
        print(monomials)
        self.monomials = {}
        self.add(*monomials)

    def add(self, *m):
        M = self.monomials
        for r in m:
            handled = False
            for l in M:
                if l.is_same(r):
                    l.add_coef(r.coef)
                    handled = True
            if not handled:
                M.append(r)

    def mul(self, *m):
        M = self.monomials
        for l in M:
            for r in m:
                l.mul(r)

    def create(expr):
        raise NotImplementedError("Must be overridden")

    def __repr__(self):
        return " + ".join(self.monomials)
    
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
        print('<<FORMULA', ty, value, operands)
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
                print('  add chlds')
            elif ty == ArithFormula.ADD and o.value_equals(0):
                continue
            elif ty == ArithFormula.MUL and o.value_equals(1):
                continue
            else:
                print('  add norm')
                self.add_child(o)


        if len(self._children) == 1 and ty != ArithFormula.NOT:
            elem = self._children.pop()
            self._value = elem._value
            self._ty = elem._ty

        #print('FORMULA>>', self)

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
        if op == ArithFormula.SLE : return "<="
        if op == ArithFormula.SLT : return "<" 
        if op == ArithFormula.ULT : return "<u" 
        if op == ArithFormula.ULE : return "<=u" 
        if op == ArithFormula.SGE : return ">="
        if op == ArithFormula.SGT : return ">" 
        if op == ArithFormula.UGT : return ">u" 
        if op == ArithFormula.UGE : return ">=u" 
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

    def distribute_inplace(self, *subs):
        """ Return True if the formula gets modified """
        changed = False
        for op in self._children:
            changed |= op.distribute_inplace(*subs)

        if not self.is_mul():
            return changed

        chlds = list(self._children)
        oldlen = len(chlds)
        c1 = chlds.pop()
        c2 = chlds.pop()

        mk_add = lambda *args: type(self)(ArithFormula.ADD, None, *args)
        mk_mul = lambda *args: type(self)(ArithFormula.MUL, None, *args)

        newf = _distribute_two(c1, c2, mk_add, mk_mul)
        while chlds:
            c = chlds.pop()
            newf = _distribute_two(newf, c, mk_add, mk_mul)

        self._ty = newf._ty
        self._children = newf._children
        assert len(self._children) >= oldlen, f"{len(self._children)}, {oldlen}"
        return len(self._children) != oldlen


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
            return And(*subexp)
        elif is_or(expr):
            return Or(*(eliminate_common_subexpr(c) for c in expr.children()))
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
        def __init__(self, coef, *variabl):
            super().__init__(coef, *variabl)

        def create(expr):
            raise NotImplementedError("Must be overridden")

    class BVPolynomial(Polynomial):
        """
        Helper class for representing formulas in LIA or BV theory.
        This class makes it easy to work with commutative expressions
        by merging the operands into sets (if the operation is commutative).
        """
        def __init__(self, *monomials):
            super().__init__(*monomials)

        def create(expr):
            print(expr)
            P = BVPolynomial()
            if is_app_of(expr, Z3_OP_BADD):
                P.add(*(BVPolynomial.create(e) for e in expr.children()))
            elif is_app_of(expr, Z3_OP_BMUL):
                P.mul(*(BVPolynomial.create(e) for e in expr.children()))
            elif is_const(expr):
                if is_bv_value(expr):
                    return BVPolynomial(BVMonomial(expr.as_long()))
                return BVPolynomial(BVMonomial(1, (expr, 1)))
            print(P)
            return P
            raise NotImplementedError("Must be overridden")

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
                    P = BVPolynomial.create(expr)
                    return BVFormula(ArithFormula.POLYNOM, P)
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
            assert op >= ArithFormula.MT_VALUES, expr
            return BVFormula(op, expr)

        def value_equals(self, x):
            v = self._value
            if v is None:
                return False
            return is_bv_value(v) and v.as_long() == x

        def expr(self):
            "Convert this object into expression for solver"
            raise NotImplementedError("Must be overridden")



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

    def replace_common_subexprs(expr_to, exprs_from):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        if not exprs_from:
            return expr_to

        try:
            to_formula = BVFormula.create(expr_to)
            print('TO', to_formula)
            while to_formula.distribute_inplace():
                print('TO d', to_formula)
                pass
            print('TO fin', to_formula)

            subs = []
            for e in exprs_from:
                e_formula = BVFormula.create(e)
                if e_formula.is_eq():
                    chlds = list(e_formula.children())
                    if chlds[0].is_mul():
                        subs.append((chlds[0], chlds[1]))
                    elif chlds[1].is_mul():
                        subs.append((chlds[1], chlds[0]))

            if not subs:
                return expr_to

            print('orig F', to_formula)
            while to_formula.substitute_inplace(*subs):
                print('F', to_formula)
                to_formula.distribute_inplace()
                print('F distr', to_formula)
            print('RESULT', to_formula)
            return to_formula.expr()
        except ValueError:
            return None, None

    def replace_arith_ops(expr):
        """
        Replace arithmetical operations with a fresh uninterpreted symbol.
        Return a mapping from new symbols to replaced expressions.
        Note: performs formula rewritings before the replacement.
        """
        try:
            atoms = {}
            expr = And(*Then("tseitin-cnf",
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
            if is_and(expr): return And(*red)
            elif is_or(expr): return Or(*red)
           #elif is_add(expr): return Sum(*red)
           #elif is_mul(expr): return Product(*red)
            else: return expr.decl()(*red)


    def reduce_eq_bitwidth(expr, bw):
        #return _reduce_eq_bitwidth(expr, bw, variables)
        try:
            # we need the expr in NNF
            expr_nnf = Tactic("nnf")(expr)
            assert len(expr_nnf) == 1, expr_nnf
            return _reduce_eq_bitwidth(And(*expr_nnf[0]), bw)
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
        return Expr(Or(*(And(*c) for c in rewrite_simplify(self._expr))), self.type())

    def split_clauses(self):
        """
        Get the expression in CNF form.
        """
        return Expr(Or(*(And(*c) for c in split_clauses(self._expr))), self.type())

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
