class MemoryProjection:
    def __init__(self, state):
        self.memory = {
            (mo_id, offset): val
            for mo_id, mo in state.memory._objects.items()
            for offset, val in mo._values.items()
        }
        self.memory.update(
            {
                (mo_id, offset): val
                for mo_id, mo in state.memory._glob_objects.items()
                for offset, val in mo._values.items()
                if not mo.is_read_only()
            }
        )

    def get(self, mo_id, offset):
        return self.memory.get((mo_id, offset))

    def items(self):
        return self.memory.items()

    def __repr__(self):
        return f"MemoryProjection {self.memory}"
