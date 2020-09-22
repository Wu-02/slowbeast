from slowbeast.ir.instruction import Cmp

class Relation:
    def __init__(self, pred, a, b, expr):
        self._pred = pred
        self.a = a
        self.b = b
        self.expr = expr

    def __eq__(self, rhs):
        return self._pred == rhs._pred and self.a == rhs.a and self.b == rhs.b

    def __str__(self):
        return "({0}) {1} ({2})".format(self.a, Cmp.predicateStr(self._pred),
                                        self.b)


