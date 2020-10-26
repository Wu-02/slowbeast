from .program import ProgramElement


class Argument(ProgramElement):
    def __init__(self):
        super(Argument, self).__init__()

    def __str__(self):
        return "a{0}".format(self.getID())

    def asValue(self):
        return "a{0}".format(self.getID())
