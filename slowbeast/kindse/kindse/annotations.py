from slowbeast.util.debugging import FIXME
from slowbeast.ir.instruction import Cmp, Load, Assume, Assert
from slowbeast.symexe.pathexecutor import AssertAnnotation

def get_subs(state):
    return {l.load : l for l in (n for n in state.getNondets() if n.isNondetLoad())}

def get_relations(state):
    rels = []
    EM = state.getExprManager()

    # FIXME not efficient, just for testing now
    values = list(state.getValuesList())
    for i in range(0, len(values)):
        for j in range(i + 1, len(values)):
            # for now, we support only Load instructions
            # as other instructions require to put into the annotation
            # also their operands

            val1 = state.get(values[i])
            val2 = state.get(values[j])

            if val1.getType() != val2.getType() or\
               val1.isPointer() or val1.isBool():
                continue

            # FIXME: do not compare exprs that has the same nondets...
            # FIXME: do some quick syntectic checks
            lt = EM.Lt(val1, val2)
            islt = state.is_sat(lt)
            expr = None
            pred = None
            if islt is False:  # val1 >= val2
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:  # val1 <= val2
                    #print(val1, '=', val2)
                    expr = EM.Eq(val1, val2)
                    pred = Cmp.EQ
                elif isgt is True:
                    #print(val1, '>=', val2)
                    expr = EM.Ge(val1, val2)
                    pred = Cmp.GE
            elif islt is True:
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:
                    #print(val1, '<=', val2)
                    expr = EM.Le(val1, val2)
                    pred = Cmp.LE

            if expr and not expr.isConstant():
                assert pred
                #rels.append(Relation(pred, values[i], values[j], expr))
                yield AssertAnnotation(expr, get_subs(state), EM)

