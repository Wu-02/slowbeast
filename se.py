from slowbeast.ir.value import Constant
from slowbeast.ir.program import *
from slowbeast.ir.bblock import *
from slowbeast.ir.instruction import *
from slowbeast.ir.function import *

from slowbeast.symexe.symbolicexecution import *

from slowbeast.util.debugging import *

if __name__ == "__main__":
    set_debugging()

    P = Program()

    ND = Function("nondet_int")
    FOO = Function("foo", 2)

    B0 = BBlock(FOO)

    A = Alloc(Constant(8, 4))
    B0.append(A)
    B0.append(Store(FOO.getArgument(0), FOO.getArgument(1)))
    B0.append(Assume(Constant(False, 1)))
    B0.append(Return(Constant(3, 2)))

    P.addFun(FOO)

    F = Function("main")

    B0 = BBlock(F)
    B1 = BBlock(F)
    B2 = BBlock(F)
    B3 = BBlock(F)

    A = Alloc(Constant(4, 4))
    B0.append(A)
    nd = Call(ND)
    cnd = Cmp(Cmp.LE, nd, Constant(2, 32))
    B0.append(nd)
    B0.append(Store(nd, A))
    B0.append(cnd)
    B0.append(Branch(cnd, B1, B2))

    L1 = Load(A, 4)
    B1.append(L1)
    ADD = Add(L1, Constant(1, 32))
    B1.append(ADD)
    B1.append(Store(ADD, A))
    L2 = Load(A, 4)
    B1.append(L2)
    B1.append(Print(L2))
    B1.append(Branch(Constant(1, 1), B2, B2))

    A1 = Alloc(Constant(8, 4))
    B2.append(A1)
    B2.append(Store(A, A1))
    L = Load(A1, 4)
    B2.append(L)
    CALL = Call(FOO, L, A1)
    B2.append(CALL)
    C = Cmp(Cmp.EQ, ADD, L2)
    B2.append(C)
    L = Load(A1, 4)
    C2 = Cmp(Cmp.EQ, A, L)
    B2.append(L)
    B2.append(C2)
    #B2.append(Assume(C, C2))
    #B2.append(Assume(Constant(False, 1), C2))
    B2.append(Branch(C, B3, B3))

    B3.append(Return(Constant(0, 4)))

    P.addFun(F)
    P.setEntry(F)

    P.dump()

    SE = SymbolicExecutor(P)
    ec = SE.run()

    print('== exited with code {0} =='.format(ec))
