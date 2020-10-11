from . expressions import ExprManager
from .. domains.symbolic import _use_z3
from .. ir.value import Constant
from .. util.debugging import FIXME

if _use_z3:
    from z3 import Solver as Z3Solver
    from z3 import sat, unsat, unknown

    def models(assumpt, *args):
        s = Z3Solver()
        for a in assumpt:
            assert a.isBool()
            s.add(a.unwrap())
        r = s.check()
        if r != sat:
            return None

        m = s.model()
        vals = []
        for a in args:
            vals.append(m[a.unwrap()])

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

    def is_sat(*args):
        s = Z3Solver()
        r = s.check(*args)
        if r == sat:
            return True
        elif r == unsat:
            return False
        elif r == unknown:
            reason = s.reason_unknown()
            if reason == 'canceled' or\
               reason == 'interrupted from keyboard':
                # If the user interrupted the computation,
                # re-raise the interrupt if it was consumed
                # in the solver so that the rest of the code
                # can react on it
                raise KeyboardInterrupt
            return reason

        return None
else:
    from pysmt.shortcuts import is_sat


# FIXME add support for incremental solving

global_expr_manager = ExprManager()


def getGlobalExprManager():
    global global_expr_manager
    return global_expr_manager


class SolverIntf:
    """ Interface of solvers """

    __slots__ = ['_exprmanager']

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
            assert x.isBool()
            assert isinstance(x.getValue(), bool)
            if x.getValue() is False:
                return False
        return True


class SymbolicSolver(SolverIntf):
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self, em=global_expr_manager):
        super(SymbolicSolver, self).__init__(em)

    def is_sat(self, *e):
        if any(map(lambda x: x.isConstant() and x.getValue() is False, e)):
            return False
        return is_sat(*(x.unwrap() for x in e if not x.isConstant()))

    def concretize(self, assumpt, *e):
        assert all(map(lambda x: not x.isConstant(), e)),\
               "Constant instead of symbolic value"
        if any(map(lambda x: x.isConstant() and x.getValue() is False, assumpt)):
            return None
        #m = smallmodels(assumpt, *e)
        m = models(assumpt, *e)
        if m is None:  # unsat
            return None
        ret = []
        for n, v in enumerate(e):
            if m[n] is None:
                ret.append(None)
            else:
                ret.append(Constant(m[n].as_long(), v.getType()))
        return ret

  # def getUnique(self, val, *e):
  #     v = self.concretize(val, *e)
  #     if self.is_sat(self.exprmanager.Ne(val, v)):
  #         return None
  #     return v

# For efficiency, we solve the True/False case incrementally
# in the state.is_sat(). Keep this code if needed for the future
# class Solver(SolverIntf):
#   """ Basic solver that calls either concrete or (some) symbolic
#       solver based on the given values
#   """
#
#   def __init__(self, em=ExprManager()):
#       super(Solver, self).__init__(em)
#       self.symbolic = SymbolicSolver(em)
#       self.concrete = ConcreteSolver(em)
#
#   def is_sat(self, *e):
#      # FIXME: check whether this part consumes a lot of time...
#      # Since concrete are True or False, we can solve them
#      # independently without any effect on the result
#      concrete = []
#      symbolic = []
#      for x in e:
#          if x.isConstant():
#              concrete.append(x)
#          else:
#              symbolic.append(x)
#
# return self.concrete.is_sat(*concrete) and
# self.symbolic.is_sat(*symbolic)


Solver = SymbolicSolver
