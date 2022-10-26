from slowbeast.domains.expr import Expr
from slowbeast.domains.exprmgr import ExpressionManager
from slowbeast.ir.types import BitVecType, FloatType
from typing import Union


class SolverIntf:
    """Interface of solvers"""

    __slots__ = "_exprmanager"

    def __init__(self, em: ExpressionManager) -> None:
        # for now we use a global expr manager
        self._exprmanager = em

    def expr_manager(self) -> ExpressionManager:
        return self._exprmanager

    def is_sat(self, *e):
        raise NotImplementedError("Must be overriden")

    def try_is_sat(self, timeout, *e):
        raise NotImplementedError("Must be overriden")

    def fresh_value(self, name: str, ty: Union[BitVecType, FloatType]) -> Expr:
        """ty = type"""
        return self._exprmanager.fresh_value(name, ty)

    def Var(self, name, ty):
        """ty = type"""
        return self._exprmanager.Var(name, ty)
