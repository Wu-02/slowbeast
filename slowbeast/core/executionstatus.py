from copy import deepcopy
from sys import stdout
from typing import TextIO


class ExecutionStatus:
    """
    The status of a state:
      READY      - ready for execution
      EXITED     - normally exited (e.g., via a call of `exit`)
      TERMINATED - terminated by an instruction (e.g., abort)
      ERROR      - hit an error condition (assertion violation, memory error, ...)
      KILLED     - killed because of an internal problem in slowbeast (e.g., an unsupported
                   instruction)

    Apart from the status, ExecutionStatus can carry also a detail about the status,
    e.g., a string that specifies why the state was killed.
    """

    READY = 1  # ready for execution
    EXITED = 2  # normally exited
    TERMINATED = 3  # terminated by instruction (abort, etc.)
    ERROR = 4  # hit an error (violated assertion, oob access, etc.)
    # hit some problem in slowbeast (e.g., unsupported instruction, etc.)
    KILLED = 5

    __slots__ = "_status", "_detail"

    def __init__(self, st: int = READY) -> None:
        self._status = st
        self._detail = None

    def copy(self) -> "ExecutionStatus":
        return deepcopy(self)

    def __eq__(self, rhs: object):
        return self._status == rhs._status and self._detail == rhs._detail

    def __hash__(self) -> int:
        return hash(self._detail) ^ hash(self._status)

    def status(self) -> int:
        return self._status

    def detail(self):
        return self._detail

    def set_error(self, e) -> None:
        self._detail = e
        self._status = ExecutionStatus.ERROR

    def set_killed(self, e) -> None:
        self._detail = e
        self._status = ExecutionStatus.KILLED

    def set_exited(self, ec) -> None:
        self._detail = ec
        self._status = ExecutionStatus.EXITED

    def set_terminated(self, reason) -> None:
        # The state terminated for some other reason than regular exit
        self._detail = reason
        self._status = ExecutionStatus.TERMINATED

    def is_error(self) -> bool:
        return self._status == ExecutionStatus.ERROR

    def is_killed(self) -> bool:
        return self._status == ExecutionStatus.KILLED

    def is_exited(self) -> bool:
        return self._status == ExecutionStatus.EXITED

    def is_terminated(self) -> bool:
        return self._status == ExecutionStatus.TERMINATED

    def is_ready(self) -> bool:
        return self._status == ExecutionStatus.READY

    def __repr__(self) -> str:
        val = self._status
        if val == ExecutionStatus.READY:
            return "READY"
        if val == ExecutionStatus.ERROR:
            return "ERROR"
        if val == ExecutionStatus.EXITED:
            return "EXITED"
        if val == ExecutionStatus.TERMINATED:
            return "TERMINATED"
        elif val == ExecutionStatus.KILLED:
            return "KILLED"
        raise RuntimeError("Invalid state status")

    def dump(self, stream: TextIO = stdout) -> None:
        stream.write(f"status: {str(self)}\n")
