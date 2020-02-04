from slowbeast.ir.value import Constant
from slowbeast.ir.types import *
from slowbeast.ir.program import *
from slowbeast.ir.bblock import *
from slowbeast.ir.instruction import *
from slowbeast.ir.function import *

from slowbeast.symexe.executionstate import SEState


FOO = Function("foo", 0)
B0 = BBlock(FOO)

A = Alloc(Constant(8, Type(4)))
B0.append(A)
B0.append(Return(Constant(3, Type(2))))

C = Call(FOO)

s1 = SEState(A)
s2 = s1.copy()

assert s1 == s2, "FAILED: Copying empty states"

s1.pushCall(C, FOO)
s1.set(A, Constant(5, Type(32)))
assert s1 != s2, "FAILED: states coparator"

s3 = s1.copy()
assert s1 == s3, "FAILED: Copying small states"

s2.addConstraint('x')
s4 = s2.copy()
s2.dump()
s4.dump()
assert s2 == s4, "FAILED: Copying states with constraints"