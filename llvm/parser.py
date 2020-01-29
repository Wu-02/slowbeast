from slowbeast.ir.program import Program
import llvmlite.binding as llvm

def _get_llvm_module(path):
    if path.endswith('.ll'):
        with open(path, 'rt') as f:
            return llvm.parse_assembly(f.read())
    else:
        with open(path, 'rb') as f:
            return llvm.parse_bitcode(f.read())

class Parser:
    def __init__(self):
        self.program = Program()

    def _parse_fun(self, m):
        pass

    def _parse_module(self, m):
        #XXX globals!
        for f in m.functions:
            self._parse_fun(f)

    def parse(self, path):
        m = _get_llvm_module(path)
        self._parse_module(m)
        return self.program

if __name__ == "__main__":
    from sys import argv
    parser = Parser()
    P = parser.parse(argv[1])
    print(P)

