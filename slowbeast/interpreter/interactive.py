from .. util.debugging import dbg


class InteractiveHandler:
    def __init__(self, interpreter):
        self.interpreter = interpreter
        self._last_query = None
        self._stop_next_time = True
        self._break_inst = []
        self._break_pathid = []

    # a helper wrapper for _id do to look-up in memory
    # (this is a bit of a hack...)
    class DummyValue:
        def __init__(self, _id):
            self._id = _id

    def _shouldSkip(self, s, newstates):
        if self._stop_next_time:
            return False
        if s.getID() in self._break_pathid:
            return False
        if s.pc.getID() in self._break_inst:
            return False
        return True

    def prompt(self, s, newstates):
        """ s = currently executed state
            newstates = states generated
        """
        try:
            return self._prompt(s, newstates)
        except EOFError:
            from sys import exit
            print("Exiting...")
            exit(0)

    def _prompt(self, s, newstates):
        if self._shouldSkip(s, newstates):
            return

        self._stop_next_time = False

        print(
            "Stopped before executing: ({0}) {1}".format(
                s.getID(), str(
                    s.pc)))
        q = input("> ")
        if q == '':
            q = self._last_query
        while not self.handle(q, s, newstates):
            q = input("> ")

        self._last_query = q

    def handle(self, q, s, newstates):
        """ Return False for new prompt (the handling was unsuccessful) """
        try:
            return self._handle(q, s, newstates)
        except KeyboardInterrupt:
            print("Interrupted")
            return False
        except Exception as e:
            print("An exception occured during handling '{0}'".format(q))
            print(str(e))
            return False
        return False

    def _handle(self, q, s, newstates):
        dbg('query: {0}'.format(q))
        query = q.split()
        if len(query) < 1:
            return False

        if query[0] in ['c', 'continue']:
            return True  # True = continute
        if query[0] in ['n', 's', 'step', 'next']:
            self._stop_next_time = True
            return True
        elif query[0] == 'p':
            self.handlePrint(query[1:], s, newstates)
        elif query[0] == 'b':
            self.handleBreak(query[1:], s, newstates)
        elif query[0] in ['l', 'list']:
            if len(query) == 1:
                i = s.pc
                n = 0
                while i and n < 5:
                    i.dump()
                    i = i.getNextInstruction()
                    n += 1
            elif query[1] in ['b', 'bblock', 'block']:
                s.pc.getBBlock().dump()
        else:
            print("Unknown query: {0}".format(q))
            print("FIXME: ... print help ...")
        return False

    def _getstate(self, i):
        for s in self.interpreter.getStates():
            if s.getID() == i:
                return s
        return None

    def handleBreak(self, query, state, newstates):
        if not query:
            print("Break on instructions: ", self._break_inst)
            print("Break on path ID: ", self._break_pathid)
        if query[0] in ['p', 'path']:
            self._break_pathid.append(int(query[1]))
            print("Break on path ID: ", self._break_pathid)
        elif query[0] in ['i', 'inst', 'instruction']:
            self._break_inst.append(int(query[1]))
            print("Break on instructions: ", self._break_inst)
        # elif query[0] in ['s', 'state']: # XXX: states do not have any unique
        # id (yet?)...

    def handlePrint(self, query, state, newstates):
        if not query:
            raise RuntimeError("Invalid arguments to print")
        if query[0] == 'states':
            print([x.getID() for x in self.interpreter.getStates()])
        elif query[0] in ['new', 'newstates']:
            print([x.getID() for x in self.interpreter.getStates()])
        elif query[0] in ['s', 'state']:
            if len(query) == 1:
                assert state, "No current state"
                s = state
            else:
                s = self._getstate(int(query[1]))
            if s:
                s.dump()
            else:
                print('No such a state')
        # elif query[0].startswith('x'):
           # FIXME need to get the Instruction first
           # if val is None:
           #    print("No such a value")
           # else:
           #    print("{0} -> {1}".format(query[0], val))
        else:
            raise NotImplementedError("Invalid print command")
