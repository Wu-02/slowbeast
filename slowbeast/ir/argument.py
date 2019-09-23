
class Argument:
    ids = 0
    def __init__(self):
        Argument.ids += 1
        self._id = Argument.ids

    def __str__(self):
        return "a{0}".format(self._id)

    def asValue(self):
        return "a{0}".format(self._id)

