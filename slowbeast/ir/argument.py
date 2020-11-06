from .program import ProgramElement


class Argument(ProgramElement):
    # def __init__(self):
    #    super().__init__()

    def __str__(self):
        return "a{0}".format(self.get_id())

    def as_value(self):
        return "a{0}".format(self.get_id())
