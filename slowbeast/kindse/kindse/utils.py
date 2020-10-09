from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.domains.symbolic import NondetLoad


def state_to_annotation(state):
    EM = state.getExprManager()
    return AssumeAnnotation(state.getConstraintsObj().asFormula(EM),
                            {l: l.load for l in state.getNondetLoads()},
                            EM)


def unify_annotations(annot1, annot2, EM, toassert=False):
    """ Take two annotations, unify their variables and "or" them together """
    Ctor = AssertAnnotation if toassert else AssumeAnnotation

    subs1 = annot1.getSubstitutions()
    subs2 = annot2.getSubstitutions()
    expr1 = annot1.getExpr()
    expr2 = annot2.getExpr()
    if 0 < len(subs2) < len(subs1) or len(subs1) == 0:
        subs1, subs2 = subs2, subs1
        expr1, expr2 = expr2, expr1

    if len(subs1) == 0:
        assert len(subs2) == 0
        return Ctor(EM.simplify(EM.Or(expr1, expr2)), {}, EM)

    subs = {}
    col = False
    for (val, instr) in subs1.items():
        instr2 = subs2.get(val)
        if instr2 and instr2 != instr:
            # collision
            freshval = EM.freshValue(
                val.name(), bw=val.getType().getBitWidth())
            ndload = NondetLoad.fromExpr(freshval, val.load, val.alloc)
            expr2 = EM.substitute(expr2, (val, ndload))
            subs[ndload] = instr2

        # always add this one
        subs[val] = instr

    # add the rest of subs2
    for (val, instr) in subs2.items():
        if not subs.get(val):
            subs[val] = instr

    return Ctor(EM.simplify(EM.Or(expr1, expr2)), subs, EM)


def states_to_annotation(states):
    a = None
    for s in states:
        EM = s.getExprManager()
        a = unify_annotations(a or AssumeAnnotation(EM.getFalse(), {}, EM),
                              state_to_annotation(s), EM)
    return a
