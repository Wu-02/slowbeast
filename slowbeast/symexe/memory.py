from slowbeast.core.memory import Memory as CoreMemory
from slowbeast.core.memoryobject import MemoryObject as CoreMO


class MemoryObject(CoreMO):
    pass


class Memory(CoreMemory):
    def createMO(self, size, nm=None, objid=None):
        """
        Create a new memory object -- may be overridden
        by child classes to create a different type of
        memory objects.
        """
        return MemoryObject(size, nm, objid)
