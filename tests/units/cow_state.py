from slowbeast.ir.value import Constant
from slowbeast.ir.types import *
from slowbeast.ir.program import *
from slowbeast.ir.bblock import *
from slowbeast.ir.instruction import *
from slowbeast.ir.function import *

from slowbeast.interpreter.executionstate import ExecutionState


FOO = Function("foo", 0)
B0 = BBlock(FOO)

A = Alloc(Constant(8, IntType(4)))
B0.append(A)
B0.append(Return(Constant(3, IntType(2))))

C = Call(FOO)

s1 = ExecutionState(A)
s2 = s1.copy()

assert s1 == s2, "FAILED: Copying empty states"

s1.pushCall(C, FOO)
s1.set(A, Constant(5, IntType(32)))
assert s1 != s2, "FAILED: states coparator"

s1.dump()
s2 = s1.copy()
s2.dump()
assert s1 == s2, "FAILED: Copying small states"
