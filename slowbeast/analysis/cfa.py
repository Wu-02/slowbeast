from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import Branch, Call

class CFA:
    """ Control flow automaton """
    class Location:
        _counter = 0
        __slots__ = "_id", "_elem"

        def __init__(self, elem=None):
            CFA.Location._counter += 1
            self._id = CFA.Location._counter
            self._elem = elem

        def __repr__(self):
            return f"l{self._id}"

    class Edge:
        __slots__ = "_source", "_target", "_type", "_elems", "_orig_elem"

        REGULAR = 1
        ASSUME = 2
        CALL = 4

        def __init__(self, ty, s, t, elem=None):
            self._type = ty
            self._source = s
            self._target = t
            # the original program element from which this edge was created
            self._orig_elem = elem
            self._elems = []

        def source(self):
            return self._source

        def target(self):
            return self._target

        def type(self):
            return self._type

        def is_assume(self):
            return self._type == CFA.Edge.ASSUME

        def is_call(self):
            return self._type == CFA.Edge.CALL

        def add_elem(self, e):
            self._elems.append(e)

        def is_noop(self):
            return len(self._elems) == 0

        def __repr__(self):
            return f"{self._source} -> {self._target}"

    class AssumeEdge(Edge):
        __slots__ = "_is_true"
        def __init__(self, s, t, elem, istrue):
            super().__init__(CFA.Edge.ASSUME, s, t, elem)
            self._is_true = istrue

        def assume_true(self):
            return self._is_true

        def assume_false(self):
            return not self._is_true

    def __init__(self, prog):
        self._locs = []
        self._edges = []

        self.build(prog)

    def build(self, prog):
        if isinstance(prog, Program):
            self.build_from_program(prog)
        elif isinstance(prog, Function):
            self.build_from_function(prog)
       #elif isinstance(prog, CFG):
       #    build_from_cfg(prog)
        return NotImplementedError(f"Invalid input to build(): {type(prog)}")

    def build_from_program(self, prog : Program):
        assert isinstance(prog, Program)
        # build a CFA for each function and then connect them with call edges
        for F in prog.funs():
            cfa = CFA(F)
            self._locs.extend(cfa._locs)
            self._edges.extend(cfa._edges)

    def build_from_function(self, fun: Function):
        assert isinstance(fun, Function)
        locs = {}
        # create locations
        for B in fun.getBBlocks():
            edges = []

            # FIXME: break on calls
            e = None
            for i in B.instructions()[:-1]:
                # break on calls
                if isinstance(i, Call):
                    if e:
                        edges.append(e)
                        tmp = CFA.Location(i)
                        e = CFA.Edge(CFA.Edge.CALL, e.target(), tmp, i)
                    else:
                        if len(edges) > 0:
                            loc1 = edges[-1].target()
                        else:
                            loc1 = CFA.Location(B)
                            self._locs.append(loc1)
                        loc2 = CFA.Location(B)
                        self._locs.append(loc2)

                        e = CFA.Edge(CFA.Edge.CALL, loc1, loc2, i)
                    e.add_elem(i)
                    self._edges.append(e)
                    e = None
                else:
                    if e is None:
                        if len(edges) > 0:
                            loc1 = edges[-1].target()
                        else:
                            loc1 = CFA.Location(B)
                            self._locs.append(loc1)
                        loc2 = CFA.Location(B)
                        self._locs.append(loc2)

                        e = CFA.Edge(CFA.Edge.REGULAR, loc1, loc2, B)
                    e.add_elem(i)
            # do not add noop edges
            if e:
                edges.append(e)

            self._edges.extend(edges)
            if edges:
                locs[B] = (edges[0].source(), edges[-1].target())

        # create CFG edges
        FIXME: we may have no edges now
        for B in fun.getBBlocks():
            l = locs[B]
            br = B.last()
            if not isinstance(br, Branch):
                e = CFA.Edge(CFA.Edge.REGULAR, l[1], CFA.Location(br), br)
                e.add_elem(br)
                self._edges.append(e)
                continue

            tsucc = locs[br.getTrueSuccessor()][0]
            fsucc = locs[br.getFalseSuccessor()][0]
            if tsucc is fsucc:
                self._edges.append(CFA.AssumeEdge(l[1], tsucc, br, True))
            else:
                # FIXME: assume True/False
                cond = br.getCondition()
                e = CFA.AssumeEdge(l[1], tsucc, br, True)
                e.add_elem(cond)
                self._edges.append(e)
                e = CFA.AssumeEdge(l[1], fsucc, br, False)
                e.add_elem(cond)
                self._edges.append(e)

    def dump(self, stream):
        print("digraph CFA {", file=stream)
        for l in self._locs:
            print(l, file=stream)
        for e in self._edges:
            label =  '\\l'.join(map(lambda s: str(s).replace('"', '\\"'), e._elems))
            if e.is_assume() and label:
                label = f"{'!' if e.assume_false() else ''}[{label}]"
            style="color=blue" if e.is_call() else ""
            print(e, f' [label="{label}", {style}]', file=stream)
        print("}", file=stream)
