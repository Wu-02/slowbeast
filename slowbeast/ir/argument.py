from . program import ProgramElement

class Argument(ProgramElement):
    ids = 0

    def __init__(self):
        super(Argument, self).__init__()
        Argument.ids += 1
        self._id = Argument.ids

    def __eq__(self, rhs):
        return self._id == rhs._id

    def __str__(self):
        return "a{0}".format(self._id)

    def __hash__(self):
        # XXX: we can never put it into a map
        # along with instructions...
        return self._id

    def asValue(self):
        return "a{0}".format(self._id)
