from copy import copy

class KindCFGPath:
    def __init__(self, cfgpath):
        self.cfgpath = cfgpath

    def newwithcfgpath(self, newpath):
        pathcopy = copy(self)
        pathcopy.cfgpath = newpath
        return pathcopy


