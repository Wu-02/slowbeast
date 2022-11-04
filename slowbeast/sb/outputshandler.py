from os import getcwd
from typing import TextIO

from slowbeast.util.debugging import new_output_file


class OutputsHandler:
    def __init__(self, testgen, outdir):
        # test generator
        self.testgen = testgen
        # where can the algorithm dump debugging data
        self.cwd = getcwd()
        self.outdir = outdir
        # stream for logging
        # self.logstream = logstream

    def new_output_file(self, name: str) -> TextIO:
        return new_output_file(name, self.outdir or self.cwd)
