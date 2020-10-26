from slowbeast.domains.symbolic import Expr
from slowbeast.ir.instruction import Instruction, Load


def _createCannonical(expr, subs, EM):
    def get_cannonic_var(val, x):
        if isinstance(x, Load):
            name = f"L({x.getOperand(0).asValue()})"
        else:
            name = x.asValue()
        return EM.Var(name, val.getBitWidth())

    return EM.substitute(
        expr, *((val, get_cannonic_var(val, x)) for (val, x) in subs.items())
    )


class StateDescription:
    """
    A description of a symbolic execution state
    as a formula + substitutions from results
    of instructions. That is, an StateDescription
    object describes the symbolic execution state
    in which holds the expression after substituing
    the results of instructions according to
    the substitutions.
    """

    __slots__ = ["_expr", "_subs"]

    def __init__(self, expr, subs):
        assert expr is not None and isinstance(expr, Expr)
        assert subs is not None and isinstance(subs, dict)

        # the expression to evaluate
        self._expr = expr

        # substitution for the expression -
        # a mapping expr -> instruction meaning that
        # state.eval(instruction) should be put on the
        # place of the key expression
        assert isinstance(subs, dict)
        assert all(map(lambda k: isinstance(k, Expr), subs.keys()))
        assert all(map(lambda k: isinstance(k, Instruction), subs.values()))
        self._subs = subs

    def cannonical(self, EM):
        return _createCannonical(self._expr, self._subs, EM)

    def getExpr(self):
        return self._expr

    def getSubstitutions(self):
        return self._subs

    def doSubs(self, state):
        """
        Return the expression after substitutions
        in the given state.
        """
        EM = state.getExprManager()
        get = state.get
        expr = self._expr
        # for (x, val) in self.subs.items():
        subs = ((v, get(x)) for (v, x) in self._subs.items())

        # we must do all the substitution at once!
        return EM.substitute(expr, *((val, curval) for (val, curval) in subs if curval))

    def __repr__(self):
        return "{0}[{1}]".format(
            self._expr,
            ", ".join(
                f"{x.asValue()}->{val.unwrap()}" for (x, val) in self.subs.items()
            ),
        )

    def dump(self):
        print("StateDescription:")
        print(f"> expr: {self._expr}")
        print(
            "> substitutions: {0}".format(
                ", ".join(
                    f"{x.asValue()} -> {val.unwrap()}"
                    for (val, x) in self._subs.items()
                )
            )
        )


def unify_state_descriptions(EM, annot1, annot2):
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
            freshval = EM.freshValue(val.name(), bw=val.getType().getBitWidth())
            expr2 = EM.substitute(expr2, (val, freshval))
            subs[freshval] = instr2

        # always add this one
        subs[val] = instr

    # add the rest of subs2
    for (val, instr) in subs2.items():
        if not subs.get(val):
            subs[val] = instr

    return EM.simplify(expr1), EM.simplify(expr2), subs
