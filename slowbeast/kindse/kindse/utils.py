from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.domains.symbolic import NondetLoad


def state_to_annotation(state):
    EM = state.getExprManager()
    return AssumeAnnotation(state.getConstraintsObj().asFormula(EM),
                            {l: l.load for l in state.getNondetLoads()},
                            EM)


def unify_annotations(EM, annot1, annot2):
    """
    Take two annotations, unify their variables and substitutions.
    Return the new expressions and the substitutions
    """
    if annot1 is None:
        return None, annot2.getExpr(), annot2.getSubstitutions()
    if annot2 is None:
        return annot1.getExpr(), None, annot1.getSubstitutions()

    # perform less substitutions if possible
    subs1 = annot1.getSubstitutions()
    subs2 = annot2.getSubstitutions()
    expr1 = annot1.getExpr()
    expr2 = annot2.getExpr()
    if 0 < len(subs2) < len(subs1) or len(subs1) == 0:
        subs1, subs2 = subs2, subs1
        expr1, expr2 = expr2, expr1

    if len(subs1) == 0:
        assert len(subs2) == 0
        return EM.simplify(expr1), EM.simplify(expr2), {}

    subs = {}
    col = False
    for (val, instr) in subs1.items():
        instr2 = subs2.get(val)
        if instr2 and instr2 != instr:
            # collision
            freshval = EM.freshValue(
                val.name(), bw=val.getType().getBitWidth())
            expr2 = EM.substitute(expr2, (val, freshval))
            subs[freshval] = instr2

        # always add this one
        subs[val] = instr

    # add the rest of subs2
    for (val, instr) in subs2.items():
        if not subs.get(val):
            subs[val] = instr

    return EM.simplify(expr1), EM.simplify(expr2), subs

def or_annotations(EM, toassert, *annots):
    assert isinstance(toassert, bool)
    assert len(annots) > 0
    if len(annots) == 1:
        return annots[0]

    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    subs = {}
    S = None
    for a in annots:
        expr1, expr2, subs = unify_annotations(EM, S, a)
        if expr1 and expr2:
            print(expr1, expr2, subs)
            S = Ctor(EM.simplify(EM.Or(expr1, expr2)), subs, EM)
        else:
            S = Ctor(expr1 or expr2, subs, EM)
    return S


def states_to_annotation(states):
    a = None
    for s in states:
        EM = s.getExprManager()
        a = or_annotations(EM, False,
                           a or AssumeAnnotation(EM.getFalse(), {}, EM),
                           state_to_annotation(s))
    return a
