from slowbeast.analysis.callgraph import CallGraph
from slowbeast.analysis.cfa import CFA
from slowbeast.analysis.dfs import DFSEdgeType, DFSVisitor
from slowbeast.analysis.scc import StronglyConnectedComponents


class ProgramStructure:
    """
    Class that contains information about control-flow and call structure
    of the program.
    """
    def __init__(self, prog, new_dbg_file=None):
        self.new_dbg_file = new_dbg_file
        callgraph = CallGraph(prog)
        if __debug__:
            with new_dbg_file("callgraph-full.txt") as f:
                callgraph.dump(f)

        callgraph.pruneUnreachable(prog.entry())
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
        # entry location of the whole program
        self.entry_loc = cfas[prog.entry()].entry()

        self.loop_headers = None

    def get_loop_headers(self):
        # FIXME: do it separately for each CFA
        headers = self.loop_headers
        if headers is None:
            headers = find_loop_headers(self.cfas, self.new_dbg_file)
            self.loop_headers = headers
        return headers


def find_loop_headers(cfas, new_output_file=None):
    headers = set()

    def processedge(edge, dfstype):
        if dfstype == DFSEdgeType.BACK:
            headers.add(edge.target())

    for cfa in cfas.values():
        SCCs = StronglyConnectedComponents(cfa)
        for C in SCCs:
            print(C)

        if __debug__:
            if new_output_file:
                with new_output_file(f"{cfa.fun().name()}-dfs.dot") as f:
                    DFSVisitor().dump(cfa, f)

        DFSVisitor().foreachedge(cfa.entry(), processedge)

    return headers