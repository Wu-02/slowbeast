from sys import stdout
from typing import TextIO

from slowbeast.util.debugging import print_stream


class ProgramElement:
    """
    Basic class for all elements of a program (functions, instructions, global values,
    basic blocks). Just anything to which we want to assign any metadata.
    """

    elemsCounter = 0

    __slots__ = "_metadata", "_id"

    def __init__(self) -> None:
        """
        Metadata is a list of tuples (key, data).
        The key is not unique (therefore its a list).
        """
        self._metadata = []

        ProgramElement.elemsCounter += 1
        self._id = ProgramElement.elemsCounter

    def metadata(self):
        return self._metadata

    def get_metadata(self, key: str):
        assert isinstance(key, str)
        for k, v in self._metadata:
            if k == key:
                return v
        return None

    def add_metadata(self, key: str, value) -> None:
        assert isinstance(key, str)
        self._metadata.append((key, value))

    def is_global(self) -> bool:
        """Is visible everywhere in the program?"""
        return False

    def get_id(self):
        return self._id

    def __eq__(self, rhs: object):
        return self._id == rhs._id

    def __ne__(self, other: object) -> bool:
        return not self.__eq__(other)

    def __hash__(self):
        return self._id

    def dump(self, ind: int = 0, stream: TextIO = stdout, color: bool = True) -> None:
        col = "GRAY" if color else "BLACK"
        for k, v in self._metadata:
            print_stream(f"{' ' * ind} ; {k} : {v}", color=col, stream=stream)
