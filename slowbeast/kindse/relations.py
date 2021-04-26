from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import IntType
from slowbeast.symexe.annotations import AssertAnnotation, get_subs
from slowbeast.solvers.solver import IncrementalSolver, getGlobalExprManager


def iter_nondet_load_pairs(state):
    loads = list(state.nondet_loads())
    for i in range(0, len(loads)):
        for j in range(i + 1, len(loads)):
            yield loads[i], loads[j]


def get_var_diff_relations(state):
    subs = get_subs(state)
    EM = state.expr_manager()
    Eq, Ne = EM.Eq, EM.Ne
    Add, Sub, Mul = EM.Add, EM.Sub, EM.Mul
    Var, simplify = EM.Var, EM.simplify
    And = EM.And

    for nd1, nd2 in iter_nondet_load_pairs(state):
        l1, l2 = nd1.value, nd2.value
        assert l1 is not l2

        if l1.is_pointer() or l2.is_pointer():
            continue

        l1name, l2name = nd1.instruction.as_value(), nd2.instruction.as_value()
        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw != bw:
            l1 = EM.SExt(l1, ConcreteInt(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, ConcreteInt(bw, bw))

        # relation between loads of the type l1 - l2 = constant
        c = Var(f"c_{l1name}_{l2name}", IntType(bw))
        expr = Eq(Sub(l2, l1), c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(EM.substitute(expr, (c, cval))), subs, EM
                )

        # relation between loads of the type l1 + l2 = constant
        expr = Eq(Add(l2, l1), c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(EM.substitute(expr, (c, cval))), subs, EM
                )

        # relation between loads of the type l1 = c*l2
        expr = Eq(Mul(c, l1), l2)
        c_concr = state.concretize_with_assumptions(
            [expr, Ne(c, ConcreteInt(0, bw))], c
        )
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(EM.substitute(expr, (c, cval))), subs, EM
                )
        # relation between loads of the type l2 = c*l1
        expr = Eq(Mul(c, l2), l1)
        c_concr = state.concretize_with_assumptions(
            [expr, Ne(c, ConcreteInt(0, bw))], c
        )
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(EM.substitute(expr, (c, cval))), subs, EM
                )

        # else:
        #    # check d*l1 + e+l2 = c
        #    d = Var(f"c_{l1name}", IntType(bw))
        #    e = Var(f"c_{l2name}", IntType(bw))
        #    expr = Eq(Add(Mul(d, l1), Mul(e, l2)), c)
        #    # we do not want the trivial solution
        #    exprchk = And(EM.Or(Ne(d, ConcreteInt(0, bw)), Ne(e, ConcreteInt(0, bw))), expr)
        #    c_concr = state.concretize_with_assumptions([exprchk], c, d, e)
        #    if state.is_sat(exprchk, Ne(c, c_concr[0])) is False and\
        #       state.is_sat(exprchk, Ne(d, c_concr[1])) is False and\
        #       state.is_sat(exprchk, Ne(e, c_concr[2])) is False:
        #        yield AssertAnnotation(
        #            simplify(EM.substitute(expr, zip((d, e, c), c_concr))), subs, EM
        #        )

        # check equalities to other loads: l1 - l2 = k*l3
        for nd3 in state.nondet_loads():
            l3 = nd3.value
            if l3 is l1 or l3 is l2 or l3.is_pointer():
                continue
            l3bw = l3.type().bitwidth()
            l3name = nd3.instruction.as_value()
            bw = max(l3bw, bw)
            if l1bw != bw:
                l1 = EM.SExt(l1, ConcreteInt(bw, bw))
            if l2bw != bw:
                l2 = EM.SExt(l2, ConcreteInt(bw, bw))
            if l3bw != bw:
                l3 = EM.SExt(l3, ConcreteInt(bw, bw))

            if state.is_sat(Ne(Sub(l2, l1), l3)) is False:
                yield AssertAnnotation(Eq(Sub(l2, l1), l3), subs, EM)
            else:
                c = EM.fresh_value(f"c_mul_{l1name}{l2name}{l3name}", IntType(bw))
                # expr = Eq(Add(l1, l2), Mul(c, l3))
                expr = And(Eq(Add(l1, l2), Mul(c, l3)), Ne(c, ConcreteInt(0, bw)))
                c_concr = state.concretize_with_assumptions([expr], c)
                if c_concr is not None:
                    # is c unique?
                    cval = c_concr[0]
                    if state.is_sat(EM.substitute(expr, (c, cval))) is False:
                        yield AssertAnnotation(
                            simplify(Eq(Add(l1, l2), Mul(cval, l3))),
                            subs,
                            EM,
                        )


def _compare_two_loads(state, l1, l2):
    subs = get_subs(state)
    EM = state.expr_manager()
    Lt, Gt, Eq, = (
        EM.Lt,
        EM.Gt,
        EM.Eq,
    )
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
            yield AssertAnnotation(simpl(Eq(l1, l2)), subs, EM)
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


# def get_var_cmp_relations(state):
#
#     # comparision relations between loads
#     for l1, l2 in iter_load_pairs(state):
#        yield from _compare_two_loads(state, l1, l2)


def _get_const_cmp_relations(state):
    EM = state.expr_manager()

    # equalities with constants
    for nd in state.nondet_loads():
        l = nd.value
        if l.is_pointer():
            continue
        lbw = l.type().bitwidth()
        c = EM.Var(f"c_coef_{nd.instruction.as_value()}", IntType(lbw))
        expr = EM.Eq(l, c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, EM.Ne(c, cval))
            if nonunique is False:
                yield (l, cval)


def _get_eq_loads(state):
    subs = get_subs(state)
    EM = state.expr_manager()
    Eq, Ne = EM.Eq, EM.Ne
    Var, simplify = EM.Var, EM.simplify

    for nd1, nd2 in iter_nondet_load_pairs(state):
        l1, l2 = nd1.value, nd2.value
        assert l1 is not l2

        if l1.is_pointer() or l2.is_pointer():
            continue

        l1name, l2name = nd1.instruction.as_value(), nd2.instruction.as_value()
        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw != bw:
            l1 = EM.SExt(l1, ConcreteInt(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, ConcreteInt(bw, bw))

        # relation between loads of the type l1 - l2 = constant
        c = Var(f"c_{l1name}_{l2name}", IntType(bw))
        if state.is_sat(Ne(l1, l2)) is False:
            yield l1, l2


def get_const_cmp_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    for l, cval in _get_const_cmp_relations(state):
        yield AssertAnnotation(EM.Eq(l, cval), subs, EM)


def get_const_subs_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    C = state.constraints()
    substitute = EM.substitute
    for l, cval in _get_const_cmp_relations(state):
        assert cval.is_concrete(), (l, cval)
        for expr in C:
            nexpr = substitute(expr, (cval, l))
            if (
                not nexpr.is_concrete()
                and expr != nexpr
                and state.is_sat(nexpr) is True
            ):
                if nexpr.isEq():
                    c1, c2 = list(nexpr.children())
                    if c1.is_concrete() or c2.is_concrete():
                        continue
                if nexpr.isOr():
                    for c in nexpr.children():
                        # only a part of the disjunction may be sat in the state
                        if state.is_sat(c) is True:
                            yield AssertAnnotation(c, subs, EM)
                else:
                    yield AssertAnnotation(nexpr, subs, EM)


def _iter_constraints(C):
    for c in C:
        if c.isOr():
            for cc in c.children():
                if cc.isEq():
                    yield cc
        elif c.isEq():
            yield c


def get_var_subs_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    C = state.constraints()
    substitute, simplify = EM.substitute, EM.simplify
    yielded = set()
    for l, r in _get_eq_loads(state):
        for expr in _iter_constraints(C):
            nexpr = substitute(expr, (r, l))
            if (
                not nexpr.is_concrete()
                and expr != nexpr
                and state.is_sat(nexpr) is True
            ):
                assert nexpr.isEq()
                c1, c2 = list(nexpr.children())
                if c1.is_concrete() or c2.is_concrete():
                    continue
                if (c1, c2) in yielded or (c2, c1) in yielded:
                    continue
                yielded.add((c1, c2))
                yield AssertAnnotation(nexpr, subs, EM)
            nexpr = substitute(expr, (l, r))
            if (
                not nexpr.is_concrete()
                and expr != nexpr
                and state.is_sat(nexpr) is True
            ):
                assert nexpr.isEq()
                c1, c2 = list(nexpr.children())
                if c1.is_concrete() or c2.is_concrete():
                    continue
                if (c1, c2) in yielded or (c2, c1) in yielded:
                    continue
                yielded.add((c1, c2))
                yield AssertAnnotation(nexpr, subs, EM)


def get_relations_to_prev_states(state, prev):
    subs = get_subs(state)
    EM = state.expr_manager()

    # relation between loads
    prevexpr = prev.translated(state).as_expr()
    # for l in state.nondet_loads():
    for l, cval in _get_const_cmp_relations(state):
        bw = l.bitwidth()
        # l2bw = l2.type().bitwidth()
        oldl = EM.Var(f"old_{l}", IntType(bw))
        oldpc = EM.substitute(prevexpr, (l, oldl))
        diff = EM.Var(f"c_diff_{l}", IntType(bw))
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
                if vdval > 0:  # old value (in later iteration) is higher
                    expr = EM.conjunction(
                        EM.Ge(l, cval),
                        EM.Le(l, EM.Add(cval, dval)),
                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval)),
                    )
                else:
                    dval = ConcreteInt(-vdval, dval.bitwidth())  # change sign
                    expr = EM.conjunction(
                        EM.Ge(l, EM.Sub(cval, dval)),
                        EM.Le(l, cval),
                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval)),
                    )
                yield AssertAnnotation(expr, subs, EM)

def _get_var_relations(safe, prevsafe=None):
    if not hasattr(safe, "__iter__"):
        safe = (safe,)
    for s in safe:
        # get and filter out those relations that make the state safe
        yield from get_var_diff_relations(s)
        yield from get_const_subs_relations(s)
        yield from get_var_subs_relations(s)
        # yield from get_var_cmp_relations(s)
        if prevsafe:
            yield from get_relations_to_prev_states(s, prevsafe)


def get_var_relations(safe, prevsafe=None, only_eq=False):
    solver = IncrementalSolver()
    toyield = set()
    Not = getGlobalExprManager().Not
    for rel in _get_var_relations(safe, prevsafe):
        expr = rel.expr()
        if only_eq and not expr.isEq():
            continue
        solver.push()
        solver.add(expr)
        yield_rel = True
        for e in (ee.expr() for ee in toyield):
            if solver.is_sat(Not(e)) is False:  # included in some previous relation
                yield_rel = False
        solver.pop()
        if yield_rel:
            solver.push()
            solver.add(Not(expr))
            # remove relations included in this one
            toyield = set(e for e in toyield if solver.is_sat(e.expr()))
            solver.pop()
            toyield.add(rel)

    for rel in toyield:
        yield rel
