from typing import Optional

from slowbeast.analysis.cfa import CFA
from slowbeast.cfkind.annotatedcfa import AnnotatedCFAPath


class BSEPath:
    __slots__ = "_edges"

    def __init__(self, *edges) -> None:
        # we keep the edges in reversed order to do efficient prepends
        # (= append in the reversed case)
        if edges:
            if len(edges) == 1:
                if isinstance(edges[0], CFA.Edge):
                    self._edges = list(edges)
                elif isinstance(edges[0], BSEPath):
                    self._edges = edges[0]._edges.copy()
                elif isinstance(edges[0], AnnotatedCFAPath):
                    self._edges = list(reversed(edges[0]))
                else:
                    raise RuntimeError(f"Invalid ctor value: {edges}")
            else:
                assert all(map(lambda e: isinstance(e, CFA.Edge), edges)), edges
                self._edges = list(reversed(edges))
        assert all(
            map(lambda x: x[1] == self[x[0]], enumerate(self))
        ), "Invalid iterators and getteres"

    def edges(self):
        return self._edges

    def copy(self) -> "BSEPath":
        n = BSEPath()
        n._edges = self._edges.copy()
        return n

    def copy_prepend(self, *edges) -> "BSEPath":
        n = self.copy()
        n.prepend(*edges)
        return n

    def prepend(self, *edges) -> None:
        self._edges.extend(edges)

    def source(self) -> Optional[CFA.Location]:
        if self._edges:
            assert self._edges[-1] == self[0]
            return self._edges[-1].source()
        return None

    def target(self) -> Optional[CFA.Location]:
        if self._edges:
            assert self._edges[0] == self[-1]
            return self._edges[0].target()
        return None

    def __getitem__(self, item: int):
        assert isinstance(item, int), item  # no slices atm
        edges = self._edges
        if item < 0:
            return edges[item + 1]
        return edges[len(edges) - item - 1]

    def __iter__(self):
        return reversed(self._edges)

    def __str__(self) -> str:
        return ";".join(map(str, self))

    def __repr__(self) -> str:
        return "<=".join(map(str, self._edges))
