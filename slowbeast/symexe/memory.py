from slowbeast.core.memory import Memory as CoreMemory
from slowbeast.symexe.memoryobject import MemoryObject


class Memory(CoreMemory):
    def create_memory_object(
        self, size, nm=None, objid=None, is_global: bool = False
    ) -> MemoryObject:
        """
        Create a new memory object -- may be overridden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid, is_global)
