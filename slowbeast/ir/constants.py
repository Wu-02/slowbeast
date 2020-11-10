from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import BoolType


def ConstantBool(c):
    return ConcreteVal(c, BoolType())


ConstantTrue = ConstantBool(True)
ConstantFalse = ConstantBool(False)