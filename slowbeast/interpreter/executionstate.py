from . memory import Memory

# class CallStack:
#     class Frame:
#         def __init__(self):
#             self.values = {}

#         def set(self, what, v):
#             self.values[what] = v

#         def get(self, v):
#             return self.values.get(v)

#     def __init__(self):
#         self._cs = []

class ExecutionState:
    def __init__(self, pc, m = Memory(), v = {}):
        # program counter
        self.pc = pc
        # state of memory
        self.memory = m
        # top-level values (values of computation of instructions)
        self.values = v

    def set(self, what, v):
        self.values[what] = v

    def get(self, v):
        return self.values.get(v)

    def read(self, frm):
        o = self.eval(frm)
        return o.read()

    def write(self, v, to):
        o = self.eval(to)
        return o.write(v)

