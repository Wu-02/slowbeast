from functools import partial

from slowbeast.solvers.symcrete import global_expr_mgr


def get_predicate(l):
    EM = global_expr_mgr()
    if l.is_sle():
        return EM.Le
    if l.is_sge():
        return EM.Ge
    if l.is_slt():
        return EM.Lt
    if l.is_sgt():
        return EM.Gt
    if l.is_ule():
        return partial(EM.Le, unsigned=True)
    if l.is_uge():
        return partial(EM.Ge, unsigned=True)
    if l.is_ult():
        return partial(EM.Lt, unsigned=True)
    if l.is_ugt():
        return partial(EM.Gt, unsigned=True)

    raise NotImplementedError(f"Unhandled predicate in expr {l}")


def _decompose_literal(l):
    isnot = False
    if l.is_not():
        isnot = True
        l = list(l.children())[0]

    if l.is_lt() or l.is_le():
        addtoleft = False
    elif l.is_gt() or l.is_ge():
        addtoleft = True
    else:
        return None, None, None, None

    chld = list(l.children())
    assert len(chld) == 2
    left, P, right = chld[0], get_predicate(l), chld[1]

    if isnot:
        addtoleft = not addtoleft
        EM = global_expr_mgr()
        binop = P

        def P(a, b):
            return EM.Not(binop(a, b))

    return left, right, P, addtoleft


class DecomposedLiteral:
    __slots__ = "left", "right", "pred", "addtoleft"

    def __init__(self, lit) -> None:
        self.left, self.right, self.pred, self.addtoleft = _decompose_literal(lit)

    def __bool__(self) -> bool:
        assert self.left is None or self.right and self.pred
        return self.left is not None

    def toformula(self):
        return self.pred(self.left, self.right)

    def bitwidth(self):
        left = self.left
        if left:
            return left.type().bitwidth()
        return None

    def extended(self, num):
        expr_mgr = global_expr_mgr()
        left, right = self.left, self.right
        if self.addtoleft:
            left = expr_mgr.Add(left, num)
        else:
            right = expr_mgr.Add(right, num)

        # try pushing further
        return self.pred(left, right)
