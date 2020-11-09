from slowbeast.util.debugging import dbgv, dbgv_sec
from slowbeast.core.executor import split_ready_states
from slowbeast.domains.symbolic import NondetLoad
from .statedescription import StateDescription, unify_state_descriptions

from copy import copy


class Annotation:
    """
    Object representing what to do/assume/assert in a state.
    """

    ASSUME = 1
    ASSERT = 2
    INSTRS = 3

    __slots__ = ["type"]

    def __init__(self, ty):
        assert ty >= Annotation.ASSUME and ty <= Annotation.INSTRS
        self.type = ty

    def isInstrs(self):
        return self.type == Annotation.INSTRS

    def isAssume(self):
        return self.type == Annotation.ASSUME

    def isAssert(self):
        return self.type == Annotation.ASSERT


class InstrsAnnotation(Annotation):
    """
    Annotation that is barely a sequence of instructions
    that should be executed
    """

    __slots__ = ["instrs"]

    def __init__(self, instrs):
        super(InstrsAnnotation, self).__init__(Annotation.INSTRS)
        self.instrs = instrs

    def instructions(self):
        return self.instrs

    def __iter__(self):
        return self.instrs.__iter__()

    def __repr__(self):
        return "[{0}]".format(", ".join(map(lambda i: i.as_value(), self.instrs)))

    def dump(self):
        print("InstrsAnnotation[")
        for i in self.instrs:
            print(f"  {i}")
        print("]")


class ExprAnnotation(Annotation):

    __slots__ = ["_sd", "cannonical"]

    def __init__(self, ty, expr, subs, EM):
        super(ExprAnnotation, self).__init__(ty)

        # state description
        self._sd = StateDescription(expr, subs)

        # cannonical form of the annotation (so that we can compare
        # annotations)
        self.cannonical = self._sd.cannonical(EM)

    def getDescr(self):
        return self._sd

    def getExpr(self):
        return self._sd.getExpr()

    def getSubstitutions(self):
        return self._sd.getSubstitutions()

    def getCannonical(self):
        return self.cannonical

    def Not(self, EM):
        n = copy(self)  # to copy the type and methods
        n._sd = StateDescription(EM.Not(self.getExpr()), self.getSubstitutions())
        n.cannonical = n._sd.cannonical(EM)
        return n

    def doSubs(self, state):
        return self._sd.doSubs(state)

    def __eq__(self, rhs):
        return self.cannonical == rhs.cannonical

    def __hash__(self):
        assert self.cannonical
        return self.cannonical.__hash__()

    def __repr__(self):
        assert self.cannonical
        return f"{self.cannonical}"
        # return "{0}[{1}]".format(self._expr, ",
        # ".join(f"{x.as_value()}/{val.unwrap()}" for (x, val) in
        # self.subs.items()))

    def dump(self):
        print(
            "ExprAnnotation[{0}]:".format(
                "assert" if self.type == Annotation.ASSERT else "assume"
            )
        )
        print(f"> expr: {self.getExpr()}")
        print(f"> cannonical: {self.getCannonical()}")
        print(
            "> substitutions: {0}".format(
                ", ".join(
                    f"{x.as_value()}/{val.unwrap()}"
                    for (val, x) in self.getSubstitutions().items()
                )
            )
        )


class AssertAnnotation(ExprAnnotation):
    def __init__(self, expr, subs, EM):
        super().__init__(Annotation.ASSERT, expr, subs, EM)

    def toAssume(self, EM):
        return AssumeAnnotation(self.getExpr(), self.getSubstitutions(), EM)

    def __repr__(self):
        return f"assert {ExprAnnotation.__repr__(self)}"


class AssumeAnnotation(ExprAnnotation):
    def __init__(self, expr, subs, EM):
        super().__init__(Annotation.ASSUME, expr, subs, EM)

    def __repr__(self):
        return f"assume {ExprAnnotation.__repr__(self)}"


def _execute_instr(executor, states, instr):
    newstates = []
    for state in states:
        # FIXME: get rid of this -- make a version of
        # execute() that does not mess with pc
        oldpc = state.pc
        assert state.isReady()
        newstates += executor.execute(state, instr)

    ready, nonready = [], []
    for x in newstates:
        x.pc = oldpc
        (ready, nonready)[0 if x.isReady() else 1].append(x)
    return ready, nonready


def _execute_instr_annotation(executor, states, annot):
    nonready = []
    for instr in annot:
        states, u = _execute_instr(executor, states, instr)
        nonready += u
    return states, nonready


def _execute_expr_annotation(executor, states, annot):
    nonready = []

    subs = annot.getSubstitutions()
    for i in set(subs.values()):
        states, nr = _execute_instr(executor, states, i)
        nonready += nr

    isassume = annot.isAssume()
    expr = annot.getExpr()
    ready = states
    states = []
    for s in ready:
        expr = annot.doSubs(s)
        if isassume:
            dbgv(f"assume {expr}")
            s = executor.assume(s, expr)
            if s:
                states.append(s)
        else:
            assert annot.isAssert()
            dbgv(f"assert {expr}")
            tr, tu = split_ready_states(executor.execAssertExpr(s, expr))
            states += tr
            nonready += tu

    return states, nonready


def execute_annotation(executor, states, annot):
    """ Execute the given annotation on states """

    assert isinstance(annot, Annotation), annot
    assert all(map(lambda s: s.isReady(), states))

    dbgv_sec(f"executing annotation:\n{annot}")

    if annot.isInstrs():
        states, nonready = _execute_instr_annotation(executor, states, annot)
    else:
        assert annot.isAssume() or annot.isAssert()
        states, nonready = _execute_expr_annotation(executor, states, annot)

    dbgv_sec()
    return states, nonready


def execute_annotations(executor, s, annots):
    assert s.isReady(), "Cannot execute non-ready state"
    oldpc = s.pc

    dbgv_sec(f"executing annotations on state {s.get_id()}")

    ready, nonready = [s], []
    for annot in annots:
        ready, nr = execute_annotation(executor, ready, annot)
        nonready += nr

    assert all(map(lambda s: s.pc is oldpc, ready))

    dbgv_sec()
    return ready, nonready


def _join_annotations(EM, Ctor, op, annots):
    assert len(annots) > 0
    if len(annots) == 1:
        return Ctor(annots[0].getExpr(), annots[0].getSubstitutions(), EM)

    simplify = EM.simplify
    subs = {}
    S = None
    for a in annots:
        expr1, expr2, subs = unify_state_descriptions(EM, S, a)
        if expr1 and expr2:
            S = Ctor(simplify(op(expr1, expr2)), subs, EM)
        else:
            S = Ctor(expr1 or expr2, subs, EM)
    return S


def unify_annotations(EM, a1, a2):
    return unify_state_descriptions(EM, a1.getDescr(), a2.getDescr())


def or_annotations(EM, toassert, *annots):
    assert isinstance(toassert, bool)
    assert all(map(lambda x: isinstance(x, ExprAnnotation), annots))

    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    return _join_annotations(EM, Ctor, EM.Or, annots)


def and_annotations(EM, toassert, *annots):
    assert isinstance(toassert, bool)
    assert all(map(lambda x: isinstance(x, ExprAnnotation), annots))

    Ctor = AssertAnnotation if toassert else AssumeAnnotation
    return _join_annotations(EM, Ctor, EM.And, annots)


def state_to_annotation(state):
    EM = state.getExprManager()
    return AssumeAnnotation(
        state.getConstraintsObj().asFormula(EM),
        {l: l.load for l in state.getNondetLoads()},
        EM,
    )


def states_to_annotation(states):
    a = None
    for s in states:
        EM = s.getExprManager()
        a = or_annotations(
            EM,
            False,
            a or AssumeAnnotation(EM.getFalse(), {}, EM),
            state_to_annotation(s),
        )
    return a
