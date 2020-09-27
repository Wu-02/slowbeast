from slowbeast.util.debugging import FIXME
from slowbeast.ir.instruction import Cmp, Load, Assume, Assert


class Relation:
    def __init__(self, pred, a, b, expr):
        self._pred = pred
        self.a = a
        self.b = b
        self.expr = expr

    def __eq__(self, rhs):
        return self._pred == rhs._pred and self.a == rhs.a and self.b == rhs.b

    def toCmpInst(self):
        return Cmp(self._pred, self.a, self.b)

    def neg(self, EM):
        return Relation(Cmp.predicateNeg(self._pred), self.a, self.b,
        EM.Not(self.expr))

    def toAssumption(self):
        cmpi = self.toCmpInst()
        return [self.a, self.b, cmpi, Assume(cmpi)]

    def toAssertion(self):
        cmpi = self.toCmpInst()
        return [self.a, self.b, cmpi, Assert(cmpi)]

    def __hash__(self):
        return "{0}{1}{2}".format(self.a.asValue(),
        Cmp.predicateStr(self._pred), self.b.asValue()).__hash__()

    def __str__(self):
        return "({0}) {1} ({2})".format(self.a, Cmp.predicateStr(self._pred),
                                        self.b)

def get_subs(state):
    return {l.load : l for l in (n for n in state.getNondets() if n.isNondetLoad())}


# FIXME: do it as iterator via yield?
def get_relations(state):
    rels = []
    EM = state.getExprManager()
    FIXME("Support also non-load annotations")

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
                rels.append((expr, get_subs(state)))

    return rels
