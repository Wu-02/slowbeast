from slowbeast.symexe.memorymodel import SymbolicMemoryModel
from slowbeast.symexe.interpreter import SEOptions
from slowbeast.termination.memory import Memory


class AisSymbolicMemoryModel(SymbolicMemoryModel):
    """
    Symbolic memory model that on-demand tracks what parts of memory were modified
    """

    def __init__(self, opts: SEOptions) -> None:
        super().__init__(opts)

    def create_memory(self) -> Memory:
        """Create a memory object that is going to be a part of a state."""
        return Memory()
