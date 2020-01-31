from . expressions import ExprManager
from .. domains.symbolic import _use_z3
if _use_z3:
    from z3 import Solver as Z3Solver
    from z3 import sat, unsat

    def is_sat(*args):
        s = Z3Solver()
        r = s.check(*args)
        assert r == sat or r == unsat, "Unhandled solver failure!"
        return r == sat
else:
    from pysmt.shortcuts import is_sat


# FIXME add support for incremental solving

class Solver:
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self):
        self.exprmanager = ExprManager()

    def getExprManager(self):
        return self.exprmanager

    def is_sat(self, *e):
        return is_sat([x._expr for x in e])

    def freshValue(self, name, bw=64):
        """ bw = bitwidth """
        return self.exprmanager.freshValue(name, bw)
