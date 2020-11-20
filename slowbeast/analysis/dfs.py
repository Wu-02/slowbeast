from .cfg import CFG


class DFSEdgeType:
    TREE = 1
    FORWARD = 2
    BACK = 3
    CROSS = 4

    def tostr(val):
        if val == DFSEdgeType.TREE:
            return "tree"
        elif val == DFSEdgeType.FORWARD:
            return "forward"
        elif val == DFSEdgeType.BACK:
            return "back"
        elif val == DFSEdgeType.CROSS:
            return "cross"


class DFSData:
    def __init__(self):
        self.visited = False
        self.innum = None
        self.outnum = None


class DFSCounter:
    def __init__(self):
        self.counter = 0


class DFSVisitor:
    """
    Visit nodes/edges in the DFS order and
    run a user-specified function on them.
    """

    def __init__(self):
        self._data = {}
        self._dfscounter = 0

    def _getdata(self, node):
        return self._data.setdefault(node, DFSData())

    # def foreach(self, fun, node=None):
    #     getdata = self._getdata
    #
    #     nddata = getdata(node)
    #     nddata.visited = True
    #
    #     fun(succ)
    #
    #     for succ in node.getSuccessors():
    #         if not getdata(succ).visited:
    #             self.foreach(fun, succ)

    def foreachedge(self, startnode, fun, backtrackfun=None):
        counter = DFSCounter()
        self._foreachedge(fun, backtrackfun, None, startnode, counter)

    def _foreachedge(self, fun, backtrackfun, prevnode, node, counter):
        getdata = self._getdata
        counter.counter += 1

        nddata = getdata(node)
        nddata.visited = True
        nddata.innum = counter.counter

        for succ in node.getSuccessors():
            succdata = getdata(succ)
            if succdata.visited:
                sin = succdata.innum
                din = nddata.innum
                assert sin is not None

                if sin < din:
                    sout = succdata.outnum
                    if sout is None:
                        fun(node, succ, DFSEdgeType.BACK)
                    elif sout < din:
                        fun(node, succ, DFSEdgeType.CROSS)
                else:
                    fun(node, succ, DFSEdgeType.FORWARD)
            else:
                fun(node, succ, DFSEdgeType.TREE)
                self._foreachedge(fun, backtrackfun, node, succ, counter)

        counter.counter += 1
        nddata.outnum = counter.counter
        if backtrackfun:
            backtrackfun(prevnode, node)

    def dump(self, cfg, outfl=None):
        out = None
        if outfl is None:
            from sys import stdout

            out = stdout
        else:
            if isinstance(outfl, str):
                out = open(out, "w")
            else:
                assert not outfl.closed, "Invalid stream"
                out = outfl
        assert out, "Do not have the output stream"
        assert not out.closed, "Invalid stream"

        def edgecol(val):
            if val == DFSEdgeType.TREE:
                return "green"
            elif val == DFSEdgeType.BACK:
                return "red"
            elif val == DFSEdgeType.FORWARD:
                return "blue"
            elif val == DFSEdgeType.CROSS:
                return "orange"
            return "black"

        def dumpdot(start, end, edgetype):
            print(
                '  {0} -> {1} [label="{2}", color="{3}"]'.format(
                    start.getBBlock().get_id(),
                    end.getBBlock().get_id(),
                    DFSEdgeType.tostr(edgetype),
                    edgecol(edgetype),
                ),
                file=out,
            )

        print("digraph {", file=out)

        # dump nodes
        for n in cfg.getNodes():
            print("  {0}".format(n.getBBlock().get_id()), file=out)

        # dump edges
        print("", file=out)
        self.foreachedge(cfg.entry(), dumpdot)

        # dump the in/out counters
        for n in cfg.getNodes():
            print(
                '  {0} [label="{0}\\nin,out = {1}, {2}"]'.format(
                    n.getBBlock().get_id(),
                    self._getdata(n).innum,
                    self._getdata(n).outnum,
                ),
                file=out,
            )

        print("}", file=out)
        if isinstance(outfl, str):
            out.close()  # we opened it
