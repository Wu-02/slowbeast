from slowbeast.symexe.memory import Memory as SEMemory


class Memory(SEMemory):
    pass


# def __init__(self):
#    super().__init__()
#    self._now_allocated = set()
#    self._now_written = set()
#    self._tracing = False

# def start_tracing(self):
#    self._tracing = True

# def stop_tracing(self):
#    self._tracing = False

# def clear_tracing(self):
#    self._now_allocated.clear()
#    self._now_written.clear()

# def _copy_to(self, new):
#    super()._copy_to(new)
#    # FIXME: use COW
#    new._now_allocated = self._now_allocated.copy()
#    new._now_written = self._now_written.copy()
#    new._tracing = self._tracing

# def now_written(self):
#    return self._now_written

# def now_allocated(self):
#    return self._now_allocated

# def allocate(self, size, instr=None, nm=None, objid=None):
#    if self._tracing:
#        self._now_allocated.add(instr)
#    return super().allocate(size, instr, nm, objid)

# def write(self, ptr, x):
#    if self._tracing:
#        self._now_written.add(ptr)
#    return super().write(ptr, x)
