from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.types import IntType
from slowbeast.ir.instruction import Load
from slowbeast.symexe.annotations import AssertAnnotation

from slowbeast.solvers.solver import Solver

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
        alloc = l.load.pointer_operand()
        load = cannonic_loads.setdefault(alloc, Load(alloc, l.type()))
        subs[l] = load

    return subs


def get_safe_subexpressions(state, unsafe):
    subs = get_subs(state)
    EM = state.expr_manager()

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


def get_var_cmp_relations(state):
    subs = get_subs(state)
    EM = state.expr_manager()

    # relation between loads
    for l1, l2 in iter_load_pairs(state):
        l1bw = l1.type().bitwidth()
        l2bw = l2.type().bitwidth()

        bw = max(l1bw, l2bw)
        if l1bw != bw:
            l1 = EM.SExt(l1, ConcreteInt(bw, bw))
        if l2bw != bw:
            l2 = EM.SExt(l2, ConcreteInt(bw, bw))

        c = EM.Var(f"c_diff_{l1.rhs_repr()}_{l2.rhs_repr()}", IntType(bw))
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

def _get_const_cmp_relations(state):
    EM = state.expr_manager()

    # equalities with constants
    for l in state.getNondetLoads():
        lbw = l.type().bitwidth()
        c = EM.Var(f"c_coef_{l.rhs_repr()}", IntType(lbw))
        expr = EM.Eq(l, c)
        c_concr = state.concretize_with_assumptions([expr], c)
        if c_concr is not None:
            # is c unique?
            cval = c_concr[0]
            nonunique = state.is_sat(expr, EM.Ne(c, cval))
            if nonunique is False:
                yield (l, cval)

def get_const_cmp_relations(state):
    EM = state.expr_manager()
    subs = get_subs(state)
    for l, cval in _get_const_cmp_relations(state):
        yield AssertAnnotation(EM.Eq(l, cval), subs, EM)


def get_relations_to_prev_states(state, prev):
    subs = get_subs(state)
    EM = state.expr_manager()

    # relation between loads
    prevexpr = prev.as_expr()
    #for l in state.getNondetLoads():
    for l, cval in _get_const_cmp_relations(state):
      bw = l.bitwidth()
      # l2bw = l2.type().bitwidth()
      oldl = EM.Var(f"old{l.rhs_repr()}", IntType(bw))
      oldpc = EM.substitute(prevexpr, (l, oldl))
      diff = EM.Var(f"c_diff_{l.rhs_repr()}", IntType(bw))
      expr = EM.Eq(EM.Sub(oldl, l), diff)
      diff_concr = state.concretize_with_assumptions([oldpc, expr], diff)
      has_general = False
      if diff_concr is not None:
          # is c unique?
          dval = diff_concr[0]
          vdval = dval.value()
          # convert the number from 2's complement bitvector to python int
          if vdval > (1 << (bw - 1)):
            vdval -= (1 << bw)
          if -1 <= vdval <= 1:
              continue # we do not need to replace these
          nonunique = state.is_sat(expr, oldpc, EM.Ne(diff, dval))
          diff = EM.Var(f"c_diff_{l.rhs_repr()}", IntType(bw))
          if nonunique is False:
              print(dval, vdval, cval)
              if vdval > 0: # old value is higher
                  expr = EM.conjunction(EM.Ge(l, cval),
                                        EM.Le(l, EM.Add(cval, dval)),
                                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval))
                                        )
              else:
                  expr = EM.conjunction(EM.Ge(l, cval),
                                        EM.Le(l, EM.Sub(cval, dval)),
                                        EM.Eq(EM.Rem(l, dval), EM.Rem(cval, dval))
                                        )
              print('Added', expr)
              yield AssertAnnotation(expr, subs, EM)
              has_general = True
      if not has_general:
            yield AssertAnnotation(
                EM.simplify(EM.Eq(l, cval)), subs, EM)



def get_safe_relations(safe, unsafe, prevsafe=None):
    for s in safe:
        # get and filter out those relations that make the state safe
        yield from get_var_cmp_relations(s)

        if prevsafe:
            yield from get_relations_to_prev_states(s, prevsafe)
        else:
            yield from get_const_cmp_relations(s)

