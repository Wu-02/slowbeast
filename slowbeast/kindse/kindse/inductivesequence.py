from slowbeast.core.executor import PathExecutionResult
from slowbeast.symexe.pathexecutor import AssumeAnnotation, AssertAnnotation
from slowbeast.util.debugging import print_stdout, dbg, dbg_sec
from slowbeast.solvers.solver import getGlobalExprManager
from . utils import unify_annotations

class InductiveSequence:
    """
    A path that sumarizes several paths into
    a sequence of sets of states such that
    the or of this sequence is inductive on a
    given location.
    """
    class Frame:
        """
        A frame is a pair 'states' and their
        inductive strengthening.
        """
        def __init__(self, states, strengthening):
            assert states, "BUG: empty states"
            self.states = states
            self.strengthening = strengthening

        def toannot(self):
            EM = getGlobalExprManager()
            states = self.states
            stren = self.strengthening

            assert stren is None or\
                   states.getSubstitutions() == stren.getSubstitutions()
            expr = EM.And(states.getExpr(), stren.getExpr())\
                    if stren else states.getExpr()
            return expr, states.getSubstitutions()

        def toassert(self):
            EM = getGlobalExprManager()
            return AssertAnnotation(*self.toannot(), EM)

        def toassume(self):
            EM = getGlobalExprManager()
            return AssumeAnnotation(*self.toannot(), EM)

        def strengthen(self, annot):
            EM = getGlobalExprManager()
            s = self.strengthening
            if s is None:
                self.strengthening = annot
            assert False, "Not implemented"
           #newexpr = EM.And(e, s.getExpr())
           #FIXME: need to unify the expressions
           #self.strengthening = AssertAnnotation(newexpr,
           #                                      s.getSubstitutions(),
           #                                      EM)

        def __eq__(self, rhs):
            return self.states == rhs.states and\
                   self.strengthening == rhs.strengthening

        def __repr__(self):
            return f"{self.states} with {self.strengthening}"

    def __init__(self, fst=None):
        self.frames = []
        if fst:
            # the first frame is supposed to be inductive
            self.frames.append(InductiveSequence.Frame(fst, None))

    def copy(self):
        n = InductiveSequence()
        n.frames = self.frames.copy()
        return n

    def append(self, states, strength):
        self.frames.append(InductiveSequence.Frame(states, strength))

    def strengthen(self, annot, idx):
        assert idx < len(self.frames)
        self.frames[idx].strengthen(annot)

    def toannotation(self, toassert=True):
        EM = getGlobalExprManager()
        S = None
        C = AssertAnnotation if toassert else AssumeAnnotation
        for f in self.frames:
            S = unify_annotations(S or C(EM.getFalse(), {}, EM),
                                  f.toassert(), EM,
                                  toassert=toassert)
        return S

    def __getitem__(self, idx):
        return self.frames[idx]

    def __iter__(self):
        return self.frames.__iter__()

    def __repr__(self):
        return "\nvv seq vv\n{0}\n^^ seq ^^\n".format("\n-----\n".join(map(str, self.frames)))

    def check_on_paths(self, executor, paths, pre=[], post=[], self_as_pre=False):
        """
        Check whether when we execute paths, we get to one of the frames
        """

        EM = getGlobalExprManager()
        result = PathExecutionResult()
        frames = self.frames
        selfassert = self.toannotation(toassert=True)
        for path in paths:
            p = path.copy()
            # the post-condition is the whole frame
            p.addPostcondition(selfassert)
            for e in post:
                p.addPostcondition(e)

            if self_as_pre:
                p.addPrecondition(selfassert)

            for e in pre:
                p.addPrecondition(e)

            r = executor.executePath(p)

            result.merge(r)

            if r.ready:
                print_stdout(f"safe along {path}", color="GREEN")
            if r.errors:
                print_stdout(f"unsafe along {path}", color="RED")
            if not r.ready and not r.errors and not r.other:
                print_stdout(f"infeasible along {path}", color="DARK_GREEN")

        return result

    def check_last_frame(self, executor, paths, pre=[], post=[]):
        """
        Check whether when we execute paths, we get to one of the frames
        """

        EM = getGlobalExprManager()
        result = PathExecutionResult()
        frame = self.frames[-1]
        frameassert = frame.toassert()
        for path in paths:
            p = path.copy()
            # the post-condition is the whole frame
            p.addPostcondition(frameassert)
            for e in post:
                p.addPostcondition(e)

            for e in pre:
                p.addPrecondition(e)

            r = executor.executePath(p)

            result.merge(r)

           #if r.ready:
           #    print_stdout(f"safe along {path}", color="GREEN")
           #if r.errors:
           #    print_stdout(f"unsafe along {path}", color="RED")
           #if not r.ready and not r.errors and not r.other:
           #    print_stdout(f"infeasible along {path}", color="DARK_GREEN")

        return result

    def check_ind_on_paths(self, executor, paths):
        return self.check_on_paths(executor, paths, self_as_pre=True)

