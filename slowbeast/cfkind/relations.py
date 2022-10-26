from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.ir.instruction import Load
from slowbeast.ir.types import BitVecType
from slowbeast.solvers.symcrete import IncrementalSolver, global_expr_mgr
from slowbeast.symexe.annotations import AssertAnnotation, get_subs


def iter_nondet_load_pairs(state):
    loads = list(state.nondet_loads())
    for i in range(0, len(loads)):
        for j in range(i + 1, len(loads)):
            yield loads[i], loads[j]


# def iter_concrete_pointers(state):
#     vals = list(state.memory.get_cs().values_list())
#     for i in range(0, len(vals)):
#         p1 = state.try_eval(vals[i])
#         if not(p1 and p1.is_concrete() and p1.is_pointer()):
#             continue
#         for j in range(i + 1, len(vals)):
#             p2 = state.try_eval(vals[j])
#             if p2 and p2.is_concrete() and p2.is_pointer():
#                 yield vals[i], vals[j]
def get_loads(state):
    vals = state.memory.get_cs().values_list()
    for v in vals:
        if isinstance(v, Load):
            yield v


def iter_loads(state):
    vals = list(state.memory.get_cs().values_list())
    for i in range(0, len(vals)):
        if not isinstance(vals[i], Load):
            continue
        for j in range(i + 1, len(vals)):
            if isinstance(vals[j], Load):
                yield vals[i], vals[j]


def get_var_diff_relations(state):
    subs = get_subs(state)
    expr_mgr = state.expr_manager()
    Eq, Ne = expr_mgr.Eq, expr_mgr.Ne
    Add, Sub, Mul = expr_mgr.Add, expr_mgr.Sub, expr_mgr.Mul
    Var, simplify, substitute = (
        expr_mgr.symbolic_value,
        expr_mgr.simplify,
        expr_mgr.substitute,
    )
    And = expr_mgr.And

    solver = IncrementalSolver()
    solver.add(*state.constraints())

    def model(assumptions, *e):
        return solver.concretize(assumptions, *e)

    is_sat = solver.is_sat
    try_is_sat = solver.try_is_sat

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
            l1 = expr_mgr.SExt(l1, ConcreteBitVec(bw, bw))
        if l2bw != bw:
            l2 = expr_mgr.SExt(l2, ConcreteBitVec(bw, bw))

        # relation between loads of the type l1 - l2 = constant
        c = Var(f"c_{l1name}_{l2name}", BitVecType(bw))
        expr = Eq(Sub(l2, l1), c)
        c_concr = model([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(substitute(expr, (c, cval))), subs, expr_mgr
                )

        # relation between loads of the type l1 + l2 = constant
        expr = Eq(Add(l2, l1), c)
        c_concr = model([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = is_sat(expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(substitute(expr, (c, cval))), subs, expr_mgr
                )

        # relation between loads of the type l1 = c*l2
        expr = Eq(Mul(c, l1), l2)
        c_concr = model([expr, Ne(c, ConcreteBitVec(0, bw))], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = try_is_sat(500, expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(substitute(expr, (c, cval))), subs, expr_mgr
                )
        # relation between loads of the type l2 = c*l1
        expr = Eq(Mul(c, l2), l1)
        c_concr = model([expr, Ne(c, ConcreteBitVec(0, bw))], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = try_is_sat(500, expr, Ne(c, cval))
            if nonunique is False:
                yield AssertAnnotation(
                    simplify(substitute(expr, (c, cval))), subs, expr_mgr
                )

        # check equalities to other loads: l1 - l2 = k*l3
        for nd3 in state.nondet_loads():
            l3 = nd3.value
            if l3 is l1 or l3 is l2 or l3.is_pointer():
                continue
            l3bw = l3.type().bitwidth()
            l3name = nd3.instruction.as_value()
            bw = max(l3bw, bw)
            if l1bw != bw:
                l1 = expr_mgr.SExt(l1, ConcreteBitVec(bw, bw))
            if l2bw != bw:
                l2 = expr_mgr.SExt(l2, ConcreteBitVec(bw, bw))
            if l3bw != bw:
                l3 = expr_mgr.SExt(l3, ConcreteBitVec(bw, bw))

            if is_sat(Ne(Sub(l2, l1), l3)) is False:
                yield AssertAnnotation(Eq(Sub(l2, l1), l3), subs, expr_mgr)
            else:
                c = expr_mgr.fresh_value(
                    f"c_mul_{l1name}{l2name}{l3name}", BitVecType(bw)
                )
                # expr = Eq(Add(l1, l2), Mul(c, l3))
                expr = And(Eq(Add(l1, l2), Mul(c, l3)), Ne(c, ConcreteBitVec(0, bw)))
                c_concr = model([expr], c)
                if c_concr is not None:
                    # is c unique?
                    cval = c_concr[0]
                    if is_sat(expr_mgr.substitute(expr, (c, cval))) is False:
                        yield AssertAnnotation(
                            simplify(Eq(Add(l1, l2), Mul(cval, l3))),
                            subs,
                            expr_mgr,
                        )


def _get_nd_val(l, lbw: int, Ss):
    nd1 = Ss.nondet(l)
    if not nd1:
        ndval = Ss.solver().fresh_value(f"nd{l.as_value()}", BitVecType(8 * lbw))
        Ss.create_nondet(l, ndval)
    else:
        ndval = nd1.value
    return ndval


def _do_load(state, l):
    op = state.try_eval(l.operand(0))
    if not op:
        return None
    lval, err = state.memory.read(op, l.bytewidth())
    if err:
        return None
    return lval


def _compare_two_loads(state, S, l1, l2):
    EM = state.expr_manager()
    Sub, Eq, Not = (
        EM.Sub,
        EM.Eq,
        EM.Not,
    )
    simpl = EM.simplify

    l1bw = l1.type().bytewidth()
    l2bw = l2.type().bytewidth()
    if l1bw != l2bw:
        return

    l1val = _do_load(state, l1)
    l2val = _do_load(state, l2)

    expr = Eq(l1val, l2val)
    Ss = S.get_se_state()
    if state.is_sat(Not(expr)) is False:
        ndval1, ndval2 = _get_nd_val(l1, l1bw, Ss), _get_nd_val(l2, l2bw, Ss)
        subs = get_subs(Ss)
        yield AssertAnnotation(simpl(Eq(ndval1, ndval2)), subs, EM)

    solver = IncrementalSolver()
    solver.add(*state.constraints())
    is_sat = solver.is_sat

    def model(assumptions, *e):
        return solver.concretize(assumptions, *e)

    c = EM.symbolic_value(
        f"c_coef_{l1.as_value()}{l2.as_value()}", BitVecType(8 * l1bw)
    )
    expr = Eq(Sub(l1val, l2val), c)
    c_concr = model([expr], c)
    if c_concr is not None:
        # is c unique?
        cval = c_concr[0]
        nonunique = is_sat(expr, EM.Ne(c, cval))
        if nonunique is False:
            ndval1, ndval2 = _get_nd_val(l1, l1bw, Ss), _get_nd_val(l2, l2bw, Ss)
            subs = get_subs(Ss)
            yield AssertAnnotation(simpl(Eq(Sub(ndval1, ndval2), cval)), subs, EM)


# lt = state.is_sat(Lt(l1, l2))
# gt = state.is_sat(Gt(l1, l2))

# if lt is False:  # l1 >= l2
#    if gt is False:  # l1 <= l2
#        yield AssertAnnotation(simpl(Eq(l1, l2)), subs, expr_mgr)
#    elif gt is True:  # l1 >= l2
#        if state.is_sat(Eq(l1, l2)) is False:
#            yield AssertAnnotation(simpl(Gt(l1, l2)), subs, expr_mgr)
#        else:
#            yield AssertAnnotation(simpl(expr_mgr.Ge(l1, l2)), subs, expr_mgr)
# elif lt is True:
#    if gt is False:  # l1 <= l2
#        if state.is_sat(Eq(l1, l2)) is False:
#            yield AssertAnnotation(simpl(Lt(l1, l2)), subs, expr_mgr)
#        else:
#            yield AssertAnnotation(simpl(expr_mgr.Le(l1, l2)), subs, expr_mgr)


def get_var_cmp_relations(state, S):
    # comparision relations between loads
    rels = set()
    for p1, p2 in iter_loads(state):
        for rel in _compare_two_loads(state, S, p1, p2):
            if rel not in rels:
                rels.add(rel)
                yield rel


def _get_const_cmp_relations(state):
    expr_mgr = state.expr_manager()

    solver = IncrementalSolver()
    solver.add(*state.constraints())

    def model(assumptions, *e):
        return solver.concretize(assumptions, *e)

    is_sat = solver.is_sat

    # equalities with constants
    for nd in state.nondet_loads():
        l = nd.value
        if l.is_pointer():
            continue
        lbw = l.type().bitwidth()
        c = expr_mgr.fresh_value(f"c_coef_{nd.instruction.as_value()}", BitVecType(lbw))
        expr = expr_mgr.Eq(l, c)
        c_concr = model([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = is_sat(expr, expr_mgr.Ne(c, cval))
            if nonunique is False:
                yield (l, cval)


def _get_eq_loads(state, is_sat):
    EM = state.expr_manager()
    Ne = EM.Ne

    for nd1, nd2 in iter_nondet_load_pairs(state):
        l1, l2 = nd1.value, nd2.value
        assert l1 is not l2

        if l1.is_pointer() or l2.is_pointer():
            continue

        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw != bw:
            l1 = EM.SExt(l1, ConcreteBitVec(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, ConcreteBitVec(bw, bw))

        # relation between loads of the type l1 - l2 = constant
        if is_sat(Ne(l1, l2)) is False:
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
                if nexpr.is_eq():
                    c1, c2 = list(nexpr.children())
                    if c1.is_concrete() or c2.is_concrete():
                        continue
                if nexpr.is_or():
                    for c in nexpr.children():
                        # only a part of the disjunction may be sat in the
                        # state
                        if state.is_sat(c) is True:
                            yield AssertAnnotation(c, subs, EM)
                else:
                    yield AssertAnnotation(nexpr, subs, EM)


def _iter_constraints(C):
    for c in C:
        if c.is_or():
            for cc in c.children():
                if cc.is_eq():
                    yield cc
        elif c.is_eq():
            yield c


def get_var_subs_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    C = state.constraints()
    substitute = EM.substitute

    solver = IncrementalSolver()
    solver.add(*state.constraints())
    is_sat = solver.is_sat

    yielded = set()
    for l, r in _get_eq_loads(state, is_sat):
        for expr in _iter_constraints(C):
            nexpr = substitute(expr, (r, l))
            if not nexpr.is_concrete() and expr != nexpr and is_sat(nexpr) is True:
                assert nexpr.is_eq()
                c1, c2 = list(nexpr.children())
                if c1.is_concrete() or c2.is_concrete():
                    continue
                if (c1, c2) in yielded or (c2, c1) in yielded:
                    continue
                yielded.add((c1, c2))
                yield AssertAnnotation(nexpr, subs, EM)
            nexpr = substitute(expr, (l, r))
            if not nexpr.is_concrete() and expr != nexpr and is_sat(nexpr) is True:
                assert nexpr.is_eq()
                c1, c2 = list(nexpr.children())
                if c1.is_concrete() or c2.is_concrete():
                    continue
                if (c1, c2) in yielded or (c2, c1) in yielded:
                    continue
                yielded.add((c1, c2))
                yield AssertAnnotation(nexpr, subs, EM)


def get_relations_to_prev_states(state, prev):
    subs = get_subs(state)
    expr_mgr = state.expr_manager()
    Eq, Le, Ge = expr_mgr.Eq, expr_mgr.Le, expr_mgr.Ge
    Add, Sub, Rem = expr_mgr.Add, expr_mgr.Sub, expr_mgr.Rem
    Var, substitute = expr_mgr.symbolic_value, expr_mgr.substitute
    conjunction = expr_mgr.conjunction

    solver = IncrementalSolver()
    solver.add(*state.constraints())

    def model(assumptions, *e):
        return solver.concretize(assumptions, *e)

    is_sat = solver.is_sat

    # relation between loads
    prevexpr = prev.translated(state).as_expr()
    # for l in state.nondet_loads():
    for l, cval in _get_const_cmp_relations(state):
        bw = l.bitwidth()
        # l2bw = l2.type().bitwidth()
        oldl = Var(f"old_{l}", BitVecType(bw))
        oldpc = substitute(prevexpr, (l, oldl))
        diff = Var(f"c_diff_{l}", BitVecType(bw))
        expr = Eq(Sub(oldl, l), diff)
        diff_concr = model([oldpc, expr], diff)
        if diff_concr is not None:
            # is c unique?
            dval = diff_concr[0]
            vdval = dval.value()
            # convert the number from 2's complement bitvector to python int
            if vdval > (1 << (bw - 1)):
                vdval -= 1 << bw
            if -1 <= vdval <= 1:
                continue  # we do not need to replace these
            nonunique = is_sat(expr, oldpc, expr_mgr.Ne(diff, dval))
            if nonunique is False:
                if vdval > 0:  # old value (in later iteration) is higher
                    expr = conjunction(
                        Ge(l, cval),
                        Le(l, Add(cval, dval)),
                        Eq(Rem(l, dval), Rem(cval, dval)),
                    )
                else:
                    dval = ConcreteBitVec(-vdval, dval.bitwidth())  # change sign
                    expr = conjunction(
                        Ge(l, Sub(cval, dval)),
                        Le(l, cval),
                        Eq(Rem(l, dval), Rem(cval, dval)),
                    )
                yield AssertAnnotation(expr, subs, expr_mgr)


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


def get_var_relations(safe, prevsafe=None, only_eq: bool = False):
    solver = IncrementalSolver()
    toyield = set()
    Not = global_expr_mgr().Not
    for rel in _get_var_relations(safe, prevsafe):
        expr = rel.expr()
        if only_eq and not expr.is_eq():
            continue
        solver.push()
        solver.add(expr)
        yield_rel = True
        for e in (ee.expr() for ee in toyield):
            if (
                solver.try_is_sat(300, Not(e)) is False
            ):  # included in some previous relation
                yield_rel = False
        solver.pop()
        if yield_rel:
            solver.push()
            solver.add(Not(expr))
            # remove relations included in this one
            toyield = set(
                e for e in toyield if solver.try_is_sat(300, e.expr()) is not False
            )
            solver.pop()
            toyield.add(rel)

    for rel in toyield:
        yield rel
