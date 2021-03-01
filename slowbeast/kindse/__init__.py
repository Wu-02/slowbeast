from slowbeast.symexe.symbolicexecution import SEOptions

class KindSEOptions(SEOptions):
    __slots__ = "step"

    def __init__(self, opts=None, step=-1):
        super().__init__(opts)
        self.step = step
