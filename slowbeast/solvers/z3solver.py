from typing import Optional

from z3 import sat, unsat, unknown, Solver as Z3Solver, BoolVal, BitVecVal
from z3.z3 import Solver


def models(assumpt, *args):
    s = Z3Solver()
    for a in assumpt:
        assert a.is_bool()
        s.add(a.unwrap())
    r = s.check()
    if r != sat:
        return None

    m = s.model()
    vals = []
    for a in args:
        c = m[a.unwrap()]
        if c is None:
            # m does not have a value for this variable
            # use 0
            c = BoolVal(False) if a.is_bool() else BitVecVal(0, a.type().bitwidth())
        vals.append(c)

    return vals


def models_inc(solver, assumpt, *args):
    solver.push()
    for a in assumpt:
        assert a.is_bool()
        if a.is_concrete():
            solver.add(a.value())
        else:
            solver.add(a.unwrap())
    r = solver.check()
    if r != sat:
        solver.pop()
        return None

    m = solver.model()
    vals = []
    for a in args:
        c = m[a.unwrap()]
        if c is None:
            # m does not have a value for this variable
            # use 0
            c = BoolVal(False) if a.is_bool() else BitVecVal(0, a.type().bitwidth())
        vals.append(c)

    solver.pop()
    return vals


def _is_sat(solver: Solver, timeout: int, *args) -> Optional[bool]:
    if solver is None:
        solver = Z3Solver()

    if timeout:
        solver.set("timeout", timeout)
        r = solver.check(*args)
        solver.set("timeout", 4294967295)  # default value
    else:
        r = solver.check(*args)

    if r == sat:
        return True
    if r == unsat:
        return False
    if r == unknown:
        reason = solver.reason_unknown()
        if reason == "interrupted from keyboard":
            # If the user interrupted the computation,
            # re-raise the interrupt if it was consumed
            # in the solver so that the rest of the code
            # can react on it
            raise KeyboardInterrupt
    return None
