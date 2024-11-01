try:
    import clang.cindex
except ImportError as e:
    raise ImportError(f"Need clang bindings: {e}")

from slowbeast.domains.concrete_bitvec import ConcreteBitVec
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import *
from slowbeast.ir.program import Program
from slowbeast.ir.types import *
from typing import Optional


class Parser:
    def __init__(self) -> None:
        self.program = Program()
        self._bblocks = {}
        self._mapping = {}
        self._funs = {}
        self._metadata_opts = ["c"]
        self._tus = {}

    def fun(self, fn: str) -> Optional[Function]:
        return self.program.fun(fn)

    def _add_mapping(self, celem, sbinst) -> None:
        if "c" in self._metadata_opts:
            sbinst.add_metadata("c", str(celem))
        assert self._mapping.get(ccode) is None, "Duplicated mapping"
        self._mapping[celem] = sbinst

    def parse(self, code) -> None:
        print(f"Parse {code}")
        index = clang.cindex.Index.create()
        tus = self._tus
        for cfile in code:
            tu = index.parse(cfile)
            print("Translation unit:", tu.spelling)
            tus[cfile] = tu
            print(tu.cursor.kind)
            print(tu.cursor.spelling)
            print(tu.cursor.location)
            for c in tu.cursor.get_children():
                print("  ", c.kind)
                print("  ", c.spelling)
                print("  ", c.location)
                print("  ", c.is_definition())
                print(dir(c))

            # succ, retty = parse_fun_ret_ty(self.llvmmodule, f.type.element_type)
            # if not succ:
            #    raise NotImplementedError(
            #        "Cannot parse function return type: {0}".format(f.type.element_type)
            #    )
            # self.program.add_fun(Function(f.spelling, len(list(f.arguments)), retty))
