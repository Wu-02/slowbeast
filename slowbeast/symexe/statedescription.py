from slowbeast.domains.symbolic import Expr
from slowbeast.ir.instruction import Instruction, Load


def _createCannonical(expr, subs, EM):
    def get_cannonic_var(val, x):
        if isinstance(x, Load):
            name = f"L({x.getOperand(0).asValue()})"
        else:
            name = x.asValue()
        return EM.Var(name, val.getBitWidth())

    return EM.substitute(expr, *((val, get_cannonic_var(val, x))
                                 for (val, x) in subs.items()))


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

    __slots__ = ['_expr', '_subs']

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
        return EM.substitute(expr, *((val, curval)
                                     for (val, curval) in subs if curval))

    def __repr__(self):
        return "{0}[{1}]".format(self._expr, ", ".join(
            f"{x.asValue()}->{val.unwrap()}" for (x, val) in self.subs.items()))

    def dump(self):
        print(
            "StateDescription:")
        print(f"> expr: {self._expr}")
        print("> substitutions: {0}".format(", ".join(
            f"{x.asValue()} -> {val.unwrap()}" for (val, x) in self._subs.items())))
