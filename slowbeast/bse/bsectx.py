from typing import Union

from slowbeast.bse.bsepath import BSEPath
from slowbeast.bse.bsestate import BSEState
from slowbeast.symexe.annotations import AssumeAnnotation


class BSEContext:
    """Class that keeps the state of BSE search"""

    __slots__ = "path", "loc_hits", "errorstate", "errordescr"

    def __init__(
        self,
        path,
        errstate: Union[BSEState, AssumeAnnotation],
        loc_hits=None,
        errdescr=None,
    ) -> None:
        """
        edge  - edge after which the error should be infeasible
        errstate - error condition
        loc_hits - number of hitting locations (usually just loop headers)
        """
        assert isinstance(errstate, (AssumeAnnotation, BSEState)), errstate
        self.path = BSEPath(path) if not isinstance(path, BSEPath) else path
        assert isinstance(self.path, BSEPath), self.path
        self.loc_hits = loc_hits or {}
        self.errorstate = errstate
        self.errordescr = errdescr

    def extension(self, path, cond) -> "BSEContext":
        """
        Derive a new context from this context - it must correctly preceed
        the current path.
        """
        assert (
            path.source().cfa() != self.path.source().cfa()
            or path.target() == self.path[0].source()
        ), f"{path};{self.path}"
        return BSEContext(path, cond, self.loc_hits.copy(), self.errordescr)

    def extend_path(self, edge) -> "BSEContext":
        """
        Derive a new context from this context - it must correctly preceed
        the current path.
        """
        assert (
            edge.source().cfa() != self.path.source().cfa()
            or edge.target() == self.path[0].source()
        ), f"{edge};{self.path}"
        return BSEContext(
            self.path.copy_prepend(edge),
            self.errorstate,
            self.loc_hits.copy(),
            self.errordescr,
        )

    def target_loc(self):
        return self.path[-1].target()

    def __repr__(self) -> str:
        return f"BSE-ctx[{self.path}:{self.errorstate}]"
