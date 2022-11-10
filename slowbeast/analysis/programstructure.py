from slowbeast.analysis.callgraph import CallGraph
from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.dfs import DFSEdgeType, DFSVisitor
from slowbeast.analysis.loops import compute_toplevel_loops
from slowbeast.ir.program import Program


class ProgramStructure:
    """
    Class that contains information about control-flow and call structure
    of the program.
    """

    def __init__(self, prog: Program, new_dbg_file=None) -> None:
        self.new_dbg_file = new_dbg_file
        callgraph = CallGraph(prog)
        if __debug__:
            with new_dbg_file("callgraph-full.txt") as f:
                callgraph.dump(f)

        callgraph.prune_unreachable(prog.entry())
        if __debug__:
            with new_dbg_file("callgraph.txt") as f:
                callgraph.dump(f)

        self.callgraph = callgraph
        cfas = CFA.from_program(prog, callgraph)
        if __debug__:
            for fun, cfa in cfas.items():
                with self.new_dbg_file(f"cfa.{fun.name()}.dot") as f:
                    cfa.dump(f)
        self.cfas = cfas
        # gather mapping from calls to call-edges
        self.calls = {
            e.elems()[0]: e for cfa in cfas.values() for e in cfa.edges() if e.is_call()
        }
        self.rets = {
            e.elems()[0]: e for cfa in cfas.values() for e in cfa.edges() if e.is_ret()
        }
        # entry location of the whole program
        self.entry_loc = cfas[prog.entry()].entry()

        self.loops = None

    def get_loop(self, loc):
        self._get_loops()
        return self.loops.get(loc)

    def get_loops(self):
        self._get_loops()
        return self.loops

    def get_loop_headers(self):
        # FIXME: get loops on demand separately for each CFA
        self._get_loops()
        return self.loops.keys()

    def get_loop_exits(self):
        # FIXME: get loops separately for each CFA
        self._get_loops()
        return [e for l in self.loops.values() for e in l.exits()]

    def _get_loops(self) -> None:
        loops = self.loops
        if loops is None:
            loops = {}
            for cfa in self.cfas.values():
                loops.update(compute_toplevel_loops(cfa))
            self.loops = loops
