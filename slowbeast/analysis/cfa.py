from slowbeast.ir.program import Program
from slowbeast.ir.function import Function
from slowbeast.ir.instruction import Branch, Call


class CFA:
    """ Control flow automaton """

    class Location:
        _counter = 0
        __slots__ = "_id", "_elem", "_successors", "_predecessors"

        def __init__(self, elem=None):
            CFA.Location._counter += 1
            self._id = CFA.Location._counter
            self._elem = elem
            self._successors = []
            self._predecessors = []

        def successors(self):
            return self._successors

        def predecessors(self):
            return self._predecessors

        def id(self):
            return self._id

        def __eq__(self, oth):
            return self._id == oth._id

        def __hash__(self):
            return self._id

        def __lt__(self, oth):
            return self._id < oth._id

        def __repr__(self):
            return f"L{self._id}"

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

        def successors(self):
            return self._target.successors()

        def predecessors(self):
            return self._target.predecessors()

        def type(self):
            return self._type

        def is_assume(self):
            return self._type == CFA.Edge.ASSUME

        def is_call(self):
            return self._type == CFA.Edge.CALL

        def add_elem(self, e):
            self._elems.append(e)

        def elems(self):
            return self._elems

        def get_elem(self, idx):
            """ Get element on index 'idx' or None if such elem does not exists """
            if idx < len(self._elems):
                return self._elems[idx]
            return None

        def is_noop(self):
            return len(self._elems) == 0

        def __len__(self):
            return len(self._elems)

        def __repr__(self):
            return f"{self._source} -> {self._target}"

        def __iter__(self):
            return self._elems.__iter__()

        def __getitem__(self, item):
            return self._elems.__getitem__(item)

    class AssumeEdge(Edge):
        __slots__ = "_is_true"

        def __init__(self, s, t, elem, istrue):
            super().__init__(CFA.Edge.ASSUME, s, t, elem)
            self._is_true = istrue

        def assume_true(self):
            return self._is_true

        def assume_false(self):
            return not self._is_true

    def __init__(self, fun : Function):
        assert isinstance(fun, Function)
        self._fun = fun
        self._locs = []
        self._edges = []
        self._entry = None

        self._build(fun)

    def fun(self):
        return self._fun

    def entry(self):
        return self._entry

    def edges(self):
        return self._edges

    def locations(self):
        return self._locs

    def from_program(prog: Program, callgraph=None):
        """
        Build CFAs from program and populate call edges
        """
        assert isinstance(prog, Program)
        # build a CFA for each function and then connect them with call edges
        cfas = { fun : CFA(fun) for fun in prog.funs() if not fun.isUndefined() }
        # FIXME: populate call edges
        return cfas

    def create_loc(self, elem=None):
        loc = CFA.Location(elem)
        self._locs.append(loc)
        return loc

    def _add_edge(self, e: Edge):
        e._target._predecessors.append(e)
        e._source._successors.append(e)
        # do we need this?
        self._edges.append(e)

    def _build(self, fun: Function):
        assert isinstance(fun, Function)
        locs = {}
        # create locations
        for B in fun.getBBlocks():
            loc1, loc2 = self.create_loc(B), self.create_loc(B)

            e = CFA.Edge(CFA.Edge.REGULAR, loc1, loc2, B)
            for i in B.instructions()[:-1]:
                # break on calls
                if isinstance(i, Call):
                    if e.is_noop():
                        e._type = CFA.Edge.CALL
                    else:
                        self._add_edge(e)
                        assert not e.is_noop()
                        # create the call edge
                        tmp = self.create_loc(B)
                        e = CFA.Edge(CFA.Edge.CALL, loc2, tmp, i)
                        loc2 = tmp
                    # populate the call edge
                    e.add_elem(i)
                    self._add_edge(e)
                    assert not e.is_noop()

                    # create a new edge
                    tmp = self.create_loc(B)
                    e = CFA.Edge(CFA.Edge.REGULAR, loc2, tmp, B)
                    loc2 = tmp
                else:
                    e.add_elem(i)
            self._add_edge(e)
            locs[B] = (loc1, loc2)

        # create CFG edges
        for B in fun.getBBlocks():
            br = B.last()
            l = locs.get(B)
            if not isinstance(br, Branch):
                e = CFA.Edge(CFA.Edge.REGULAR, l[1], self.create_loc(br), br)
                e.add_elem(br)
                self._add_edge(e)
                continue

            tsucc = locs[br.getTrueSuccessor()][0]
            fsucc = locs[br.getFalseSuccessor()][0]
            if tsucc is fsucc:
                self._add_edge(CFA.AssumeEdge(l[1], tsucc, br, True))
            else:
                # FIXME: assume True/False
                cond = br.getCondition()
                e = CFA.AssumeEdge(l[1], tsucc, br, True)
                e.add_elem(cond)
                self._add_edge(e)
                e = CFA.AssumeEdge(l[1], fsucc, br, False)
                e.add_elem(cond)
                self._add_edge(e)

        self._entry = locs.get(fun.getBBlock(0))[0]
        assert self._entry, "Do not have entry loc"

    def dump(self, stream):
        print(f'digraph CFA_{self._fun.getName()} {{', file=stream)
        print(f'  label="{self._fun.getName()}"', file=stream)
        entry = self._entry
        for l in self._locs:
            if l is entry:
                print(f"{l} [color=blue]", file=stream)
            else:
                print(l, file=stream)
        for e in self._edges:
            label = "\\l".join(map(lambda s: str(s).replace('"', '\\"'), e._elems))
            if e.is_assume() and label:
                label = f"{'!' if e.assume_false() else ''}[{label}]"
            if e.is_call():
                style = "color=blue"
            elif e.is_assume():
                style = "color=orange"
            else:
                style = ""
            print(e, f' [label="{label}", {style}]', file=stream)
        print("}", file=stream)
