from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import IntType
from slowbeast.ir.instruction import Load
from slowbeast.symexe.annotations import AssertAnnotation

from slowbeast.solvers.solver import Solver

# we want our annotations to talk about memory
# and if they talk about the same memory, to look the same
# So for every load X, we create a unique load X that we use
# instead. In other words, we map all the x1 = load X,
# x2 = load X, x3 = load X, ... to one x = load X
cannonic_loads = {}


def get_subs(state):
    global cannonic_loads
    subs = {}
    for l in state.getNondetLoads():
        alloc = l.load.pointer_operand()
        load = cannonic_loads.setdefault(alloc, Load(alloc, l.type()))
        subs[l] = load

    return subs


def get_safe_subexpressions(state, unsafe):
    subs = get_subs(state)
    EM = state.expr_manager()

    safe = set()
    solver = Solver()
    for c in state.getConstraints():
        # FIXME: do it somehow smarter than iterating over all...

        # get all boolean subexpressions of 'c'
        for sub in (s for s in c.subexpressions() if s.is_bool()):
            # rule out subexpressions that are not "entire"
            if not (state.is_sat(sub) is True):
                continue
            for u in unsafe:
                # if this subexpression is able to rule out some unsafe state,
                # this is our "safe" candidate
                if any(map(lambda u: u.is_sat(sub) is False, unsafe)):
                    # if it is implied by some of the safe abstractions that we
                    # already yielded, skip it
                    if any(
                        map(
                            lambda s: solver.is_sat(EM.And(sub, EM.Not(s))) is False,
                            safe,
                        )
                    ):
                        continue

                    sub = EM.simplify(sub)
                    safe.add(sub)
                    yield AssertAnnotation(sub, subs, EM)


def iter_load_pairs(state):
    loads = list(state.getNondetLoads())
    for i in range(0, len(loads)):
        for j in range(i + 1, len(loads)):
            yield loads[i], loads[j]


def get_var_diff_relations(state):
    subs = get_subs(state)
    EM = state.expr_manager()

    # relation between loads of the type l1 - l2 = constant
    for l1, l2 in iter_load_pairs(state):
        l1name, l2name = l1.rhs_repr(), l2.rhs_repr()
        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw != bw:
            l1 = EM.SExt(l1, ConcreteInt(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, ConcreteInt(bw, bw))

        c = EM.Var(f"c_diff_{l1name}_{l2name}", IntType(bw))
        expr = EM.Eq(EM.Sub(l2, l1), c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, EM.Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    EM.simplify(EM.substitute(expr, (c, cval))), subs, EM
                )
           #else:
           #    # check d*l1 + e+l2 = c
           #    d = EM.Var(f"c_{l1name}", IntType(bw))
           #    e = EM.Var(f"c_{l2name}", IntType(bw))
           #    expr = EM.Eq(EM.Add(EM.Mul(d, l1), EM.Mul(e, l2)), c)
           #    # we do not want the trivial solution
           #    exprchk = EM.And(EM.Or(EM.Ne(d, ConcreteInt(0, bw)), EM.Ne(e, ConcreteInt(0, bw))), expr)
           #    c_concr = state.concretize_with_assumptions([exprchk], c, d, e)
           #    if state.is_sat(exprchk, EM.Ne(c, c_concr[0])) is False and\
           #       state.is_sat(exprchk, EM.Ne(d, c_concr[1])) is False and\
           #       state.is_sat(exprchk, EM.Ne(e, c_concr[2])) is False:
           #        yield AssertAnnotation(
           #            EM.simplify(EM.substitute(expr, zip((d, e, c), c_concr))), subs, EM
           #        )




        # check equalities to other loads: l1 - l2 = k*l3
        for l3 in state.getNondetLoads():
            l3bw = l3.type().bitwidth()
            l3name = l3.rhs_repr()
            bw = max(l3bw, bw)
            if l1bw != bw:
                l1 = EM.SExt(l1, ConcreteInt(bw, bw))
            if l2bw != bw:
                l2 = EM.SExt(l2, ConcreteInt(bw, bw))
            if l3bw != bw:
                l3 = EM.SExt(l3, ConcreteInt(bw, bw))

            if state.is_sat(EM.Ne(EM.Sub(l2, l1), l3)) is False:
                yield AssertAnnotation(EM.Eq(EM.Sub(l2, l1), l3), subs, EM)
            else:
                if state.is_sat(EM.Ne(EM.Sub(l1, l2), l3)) is False:
                    yield AssertAnnotation(EM.Eq(EM.Sub(l1, l2), l3), subs, EM)
                else:
                    c = EM.Var(f"c_mul_{l1name}{l2name}{l3name}", IntType(bw))
                    #expr = EM.Eq(EM.Add(l1, l2), EM.Mul(c, l3))
                    expr = EM.And(EM.Eq(EM.Add(l1, l2), EM.Mul(c, l3)), EM.Ne(c, ConcreteInt(0, bw)))
                    c_concr = state.concretize_with_assumptions([expr], c)
                    if c_concr is not None:
                        # is c unique?
                        cval = c_concr[0]
                        if state.is_sat(EM.substitute(expr, (c, cval))) is False:
                            yield AssertAnnotation(
                                EM.simplify(EM.Eq(EM.Add(l1, l2), EM.Mul(cval, l3))), subs, EM
                            )


def _compare_two_loads(state, l1, l2):
    subs = get_subs(state)
    EM = state.expr_manager()
    Lt, Gt, Eq, = EM.Lt, EM.Gt, EM.Eq
    simpl = EM.simplify

    l1bw = l1.type().bitwidth()
    l2bw = l2.type().bitwidth()

    bw = max(l1bw, l2bw)
    if l1bw != bw:
        l1 = EM.SExt(l1, ConcreteInt(bw, bw))
    if l2bw != bw:
        l2 = EM.SExt(l2, ConcreteInt(bw, bw))

    lt = state.is_sat(Lt(l1, l2))
    gt = state.is_sat(Gt(l1, l2))

    if lt is False:  # l1 >= l2
        if gt is False:  # l1 <= l2
            yield AssertAnnotation(simpl(Eq(l1, l2)), subs, EM )
        elif gt is True:  # l1 >= l2
            if state.is_sat(Eq(l1, l2)) is False:
                yield AssertAnnotation(simpl(Gt(l1, l2)), subs, EM)
            else:
                yield AssertAnnotation(simpl(EM.Ge(l1, l2)), subs, EM)
    elif lt is True:
        if gt is False:  # l1 <= l2
            if state.is_sat(Eq(l1, l2)) is False:
                yield AssertAnnotation(simpl(Lt(l1, l2)), subs, EM)
            else:
                yield AssertAnnotation(simpl(EM.Le(l1, l2)), subs, EM)

def get_var_cmp_relations(state):

    # comparision relations between loads
    for l1, l2 in iter_load_pairs(state):
       yield from _compare_two_loads(state, l1, l2)


def _get_const_cmp_relations(state):
    EM = state.expr_manager()

    # equalities with constants
    for l in state.getNondetLoads():
        lbw = l.type().bitwidth()
        c = EM.Var(f"c_coef_{l.rhs_repr()}", IntType(lbw))
        expr = EM.Eq(l, c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, EM.Ne(c, cval))
            if nonunique is False:
                yield (l, cval)


def get_const_cmp_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    for l, cval in _get_const_cmp_relations(state):
        yield AssertAnnotation(EM.Eq(l, cval), subs, EM)


def get_relations_to_prev_states(state, prev):
    subs = get_subs(state)
    EM = state.expr_manager()

    # relation between loads
    prevexpr = prev.as_expr()
    # for l in state.getNondetLoads():
    for l, cval in _get_const_cmp_relations(state):
        bw = l.bitwidth()
        # l2bw = l2.type().bitwidth()
        oldl = EM.Var(f"old{l.rhs_repr()}", IntType(bw))
        oldpc = EM.substitute(prevexpr, (l, oldl))
        diff = EM.Var(f"c_diff_{l.rhs_repr()}", IntType(bw))
        expr = EM.Eq(EM.Sub(oldl, l), diff)
        diff_concr = state.concretize_with_assumptions([oldpc, expr], diff)
        if diff_concr is not None:
            # is c unique?
            dval = diff_concr[0]
            vdval = dval.value()
            # convert the number from 2's complement bitvector to python int
            if vdval > (1 << (bw - 1)):
                vdval -= 1 << bw
            if -1 <= vdval <= 1:
                continue  # we do not need to replace these
            nonunique = state.is_sat(expr, oldpc, EM.Ne(diff, dval))
            if nonunique is False:
                if vdval > 0:  # old value is higher
                    expr = EM.conjunction(
                        EM.Ge(l, cval),
                        EM.Le(l, EM.Add(cval, dval)),
                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval)),
                    )
                else:
                    expr = EM.conjunction(
                        EM.Ge(l, cval),
                        EM.Le(l, EM.Sub(cval, dval)),
                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval)),
                    )
                yield AssertAnnotation(expr, subs, EM)


def get_safe_relations(safe, unsafe, prevsafe=None):
    if not hasattr(safe, '__iter__'):
        safe = (safe,)
    for s in safe:
        # get and filter out those relations that make the state safe
        yield from get_var_diff_relations(s)
        #yield from get_var_cmp_relations(s)

        yield from get_const_cmp_relations(s)
        if prevsafe:
            yield from get_relations_to_prev_states(s, prevsafe)
