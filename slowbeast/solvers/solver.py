class SolverIntf:
    """Interface of solvers"""

    __slots__ = "_exprmanager"

    def __init__(self, em):
        # for now we use a global expr manager
        self._exprmanager = em

    def expr_manager(self):
        return self._exprmanager

    def is_sat(self, *e):
        raise NotImplementedError("Must be overriden")

    def try_is_sat(self, timeout, *e):
        raise NotImplementedError("Must be overriden")

    def fresh_value(self, name, ty):
        """ty = type"""
        return self._exprmanager.fresh_value(name, ty)

    def Var(self, name, ty):
        """ty = type"""
        return self._exprmanager.Var(name, ty)

