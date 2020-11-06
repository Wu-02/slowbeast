from slowbeast.ir.instruction import Load
from slowbeast.symexe.annotations import AssertAnnotation
from slowbeast.core.executor import PathExecutionResult

from slowbeast.util.debugging import print_stdout, dbg, dbg_sec
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath
from slowbeast.solvers.solver import Solver

from .kindsebase import KindSymbolicExecutor as BaseKindSE
from .loops import SimpleLoop

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
        alloc = l.load.getPointerOperand()
        load = cannonic_loads.setdefault(alloc, Load(alloc, alloc.getSize().value()))
        subs[l] = load

    return subs


def get_safe_subexpressions(state, unsafe):
    subs = get_subs(state)
    EM = state.getExprManager()

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


def get_all_relations(state):
    subs = get_subs(state)
    EM = state.getExprManager()

    for l1, l2 in iter_load_pairs(state):
        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw == bw:
            l1 = EM.SExt(l1, EM.Constant(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, EM.Constant(bw, bw))

        c = EM.Var("c_coef", bw)
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


def get_safe_relations(safe, unsafe):
    for s in safe:
        # get and filter out those relations that make the state safe
        saferels = (r for r in get_all_relations(s))
        for x in saferels:
            yield x


# for s in unsafe:
#    # get and filter out those relations that make the state safe
#    EM = s.getExprManager()
#    for r in get_all_relations(s):
#        yield r.Not(EM)
