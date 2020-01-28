from pysmt.shortcuts import is_sat
from . expressions import ExprManager

class Solver:
    """
    Wrapper for SMT solver(s) used throughout this project
    """

    def __init__(self):
        self.exprmanager = ExprManager()

    def getExprManager(self):
        return self.exprmanager

    def is_sat(self, e):
        return is_sat(e._expr)

    def freshValue(self, name, bw = 64):
        """ bw = bitwidth """
        return self.exprmanager.freshValue(name, bw)


