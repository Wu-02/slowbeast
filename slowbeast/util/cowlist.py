class COWList:
    __slots__ = "data", "_ro"

    def __init__(self):
        self.data = []
        self._ro = False

    def __getitem__(self, item):
        return self.data.__getitem__(item)

    def __iter__(self):
        return self.data.__iter__()

    def append(self, item):
        if self._ro:
            self.data = self.data.copy()
            self._ro = False
        self.data.append(item)

    def copy(self):
        new = COWList()
        new.data = self.data
        new._ro = self._ro = True
        return new
