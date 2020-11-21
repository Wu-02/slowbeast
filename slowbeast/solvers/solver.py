from .expressions import ExprManager
from ..domains.symbolic import _use_z3
from ..domains.concrete import ConcreteVal
from ..util.debugging import FIXME

if _use_z3:
    from z3 import Solver as Z3Solver
    from z3 import sat, unsat, unknown
    from z3 import BitVecVal, BoolVal

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

    def smallmodels(assumpt, *args):
        s = Z3Solver()
        for a in assumpt:
            s.add(a.unwrap())
        r = s.check()
        if r != sat:
            return None

        # minimize the model
        FIXME("Add timeout to solver when minimizing model")
        vals = []
        for a in args:
            s.push()
            s.add(a.unwrap() == 0)
            if s.check() == sat:
                continue
            else:
                s.pop()

            # try to obtain a small cex
            s.push()
            s.add(a.unwrap() > 0)
            if s.check() == sat:
                mx = 1000
            else:
                mx = -1000
                s.pop()
                s.add(a.unwrap() <= 0)

            while True:
                s.push()
                if mx > 0:
                    s.add(a.unwrap() < mx)
                else:
                    s.add(a.unwrap() > mx)

                if s.check() == sat:
                    mx = int(mx / 2)
                else:
                    s.pop()
                    break

        s.check()
        m = s.model()
        vals = []
        for a in args:
            vals.append(m[a.unwrap()])

        return vals

    def _is_sat(solver, *args):
        if solver is None:
            solver = Z3Solver()
        r = solver.check(*args)
        if r == sat:
            return True
        elif r == unsat:
            return False
        elif r == unknown:
            reason = solver.reason_unknown()
            if reason == "canceled" or reason == "interrupted from keyboard":
                # If the user interrupted the computation,
                # re-raise the interrupt if it was consumed
                # in the solver so that the rest of the code
                # can react on it
                raise KeyboardInterrupt
            return reason

        return None

    def is_sat(*args):
        return _is_sat(Z3Solver(), *args)


else:
    from pysmt.shortcuts import is_sat


# FIXME add support for incremental solving

global_expr_manager = ExprManager()


def getGlobalExprManager():
    global global_expr_manager
    return global_expr_manager


class SolverIntf:
    """ Interface of solvers """

    __slots__ = ["_exprmanager"]

    def __init__(self, em=global_expr_manager):
        # for now we use a global expr manager
        self._exprmanager = em

    def getExprManager(self):
        return self._exprmanager

    def is_sat(self, *e):
        raise NotImplementedError("Must be overriden")

    def freshValue(self, name, bw=64):
        """ bw = bitwidth """
        return self._exprmanager.freshValue(name, bw)

    def Var(self, name, bw=64):
        """ bw = bitwidth """
        return self._exprmanager.Var(name, bw)


class ConcreteSolver(SolverIntf):
    """
    Just check for True/False values of concrete computation
    wrapped to the interface solver.
    """

    def __init__(self, em=ExprManager()):
        super(ConcreteSolver, self).__init__(em)

    def is_sat(self, *e):
        for x in e:
            assert x.is_bool()
            assert isinstance(x.value(), bool)
            if x.value() is False:
                return False
        return True


class SymbolicSolver(SolverIntf):
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self, em=global_expr_manager):
        super().__init__(em)

    def is_sat(self, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return is_sat(*(x.unwrap() for x in e if not x.is_concrete()))

    def concretize(self, assumpt, *e):
        assert all(
            map(lambda x: not x.is_concrete(), e)
        ), "ConcreteVal instead of symbolic value"
        if any(map(lambda x: x.is_concrete() and x.value() is False, assumpt)):
            return None
        # m = smallmodels(assumpt, *e)
        m = models(assumpt, *e)
        if m is None:  # unsat
            return None
        ret = []
        for n, v in enumerate(e):
            if m[n] is None:
                ret.append(None)
            else:
                ret.append(ConcreteVal(m[n].as_long(), v.type()))
        return ret

class IncrementalSolver(SymbolicSolver):
    def __init__(self, em=global_expr_manager):
        super().__init__(em)
        self._solver = Z3Solver()

    def add(self, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            self._solver.add(BoolVal(False))
        print(e)
        self._solver.add(*(x.unwrap() for x in e if not x.is_concrete()))

    def push(self):
        self._solver.push()

    def pop(self, num : int = 1):
        self._solver.pop(num)

    def is_sat(self, *e):
        if any(map(lambda x: x.is_concrete() and x.value() is False, e)):
            return False
        return _is_sat(self._solver, *(x.unwrap() for x in e if not x.is_concrete()))

    def concretize(self, assumpt, *e):
        raise NotImplementedError("Not implemented yet")

    def __repr__(self):
        return f"IncrementalSolver: {self._solver}"


Solver = SymbolicSolver
