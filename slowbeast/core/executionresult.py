from itertools import chain


def split_ready_states(states):
    ready, notready = [], []
    for x in states:
        (ready, notready)[0 if x.is_ready() else 1].append(x)
    return ready, notready


def split_nonready_states(states):
    errs, oth = [], []
    for x in states:
        (errs, oth)[0 if x.has_error() else 1].append(x)
    return errs or None, oth or None


class PathExecutionResult:
    """
    An object that contains sets of states obtained by executing a path
    in a program. The sets are divided according to their status:
      - ready: states that are ok after the execution of the path and can
               be further executed,
      - errors: states that contain an error (assertion violation, etc.)
                that was it in the last step of executing the path
      - early: states that were killed/terminated or hit an error before reaching
               the end of the path (i.e., these can be also error states,
               but those where the error occurred before entirely executing
               the path).
      - other: states that are not ready (were e.g., killed) in the last step
               of executing the path. So these are similar to 'errors' but
               they were killed/terminated, not reached an error.

    Other view on the division is this: 'ready', 'errors', and 'other' states made
    it through the execution of the whole path, but 'errors' states hit the error when executing
    the last instruction and 'other' states hit some other problem (abort) or terminated (these
    cannot be executed further and thus are not ready). 'early' states did not make it to the
    end of the path.
    """

    __slots__ = "ready", "errors", "early", "other"

    def __init__(self, ready=None, errors=None, early=None, other=None) -> None:
        # states that can be further executed
        self.ready = ready
        # error states that were hit during the execution
        # of the last point on the path
        self.errors = errors
        # non-ready states that were hit during the execution
        # of the path up to the last point
        # (these include error, terminated and killed states)
        self.early = early
        # other states --  these can be only the
        # killed and terminated states hit during the execution
        # of the last point on the path
        self.other = other

    def errors_to_early(self) -> None:
        """Move errors states to early states"""

        errs = self.errors
        earl = self.early
        if earl and errs:
            earl += errs
        elif errs:
            self.early = errs
        self.errors = None

    def other_to_early(self) -> None:
        """Move other states to early states"""
        oth = self.other
        earl = self.early
        if earl and oth:
            earl += oth
        elif oth:
            self.early = oth
        self.other = None

    def add(self, states) -> None:
        """
        Add 'states' to this PathExecutionResult.
        The states are automatically divided into 'ready',
        'errors', and 'other' according to their status.
        """
        ready = self.ready or []
        errs = self.errors or []
        oth = self.other or []
        for s in states:
            if s.is_ready():
                ready.append(s)
            elif s.has_error():
                errs.append(s)
            else:
                oth.append(s)
        self.ready = ready
        self.errors = errs
        self.other = oth

    def merge(self, r) -> None:
        """
        Merge two PathExecutionResults element-wise.
        """
        if r.ready:
            ready = self.ready or []
            ready += r.ready
            self.ready = ready
        if r.errors:
            errs = self.errors or []
            errs += r.errors
            self.errors = errs
        if r.early:
            erl = self.early or []
            erl += r.early
            self.early = erl
        if r.other:
            oth = self.other or []
            oth += r.other
            self.other = oth

    def killed(self):
        """Return all states from 'other' and 'early' that have the status 'killed'"""
        other = self.other
        early = self.early
        killed1 = (s for s in other if s.was_killed()) if other else ()
        killed2 = (s for s in early if s.was_killed()) if early else ()
        return chain(killed1, killed2)

    def check(self) -> bool:
        assert not self.ready or all(map(lambda x: x.is_ready(), self.ready))
        assert not self.errors or all(map(lambda x: x.has_error(), self.errors))
        assert not self.early or all(map(lambda x: not x.is_ready(), self.early))
        assert not self.other or all(
            map(lambda x: x.is_terminated() or x.was_killed() or x.exited(), self.other)
        )
        return True

    def __repr__(self) -> str:
        haveany = False
        msg = "PathExecutionResult: {"
        if self.ready:
            haveany = True
            msg += f"\n  ready: {[x.get_id() for x in self.ready]}"
        if self.errors:
            haveany = True
            msg += f"\n  errors: {[x.get_id() for x in self.errors]}"
        if self.early:
            haveany = True
            msg += f"\n  early: {[x.get_id() for x in self.early]}"
        if self.other:
            haveany = True
            msg += f"\n  other: {[x.get_id() for x in self.other]}"
        if haveany:
            msg += "\n}"
        else:
            msg += "}"

        return msg
