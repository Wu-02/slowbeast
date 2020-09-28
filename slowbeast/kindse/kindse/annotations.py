from slowbeast.ir.instruction import Cmp, Load, Assume, Assert
from slowbeast.symexe.pathexecutor import AssertAnnotation

from slowbeast.util.debugging import print_stderr, print_stdout, dbg, dbg_sec
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath

from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . paths import SimpleLoop

def get_subs(state):
    return {l.load : l for l in (n for n in state.getNondets() if n.isNondetLoad())}

def get_relations(state):
    rels = []
    EM = state.getExprManager()

    # FIXME not efficient, just for testing now
    values = list(state.getValuesList())
    for i in range(0, len(values)):
        for j in range(i + 1, len(values)):
            val1 = state.get(values[i])
            val2 = state.get(values[j])

            if val1.getType() != val2.getType() or\
               val1.isPointer() or val1.isBool():
                continue

            # FIXME: do not compare exprs that has the same nondets...
            # FIXME: do some quick syntectic checks
            # NOTE: this is not the same as generating the invariant candidate
            # from path condition. See simple-loop test
            lt = EM.Lt(val1, val2)
            islt = state.is_sat(lt)
            expr = None
            pred = None
            if islt is False:  # val1 >= val2
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:  # val1 <= val2
                    #print(val1, '=', val2)
                    expr = EM.Eq(val1, val2)
                    pred = Cmp.EQ
                elif isgt is True:
                    #print(val1, '>=', val2)
                    expr = EM.Ge(val1, val2)
                    pred = Cmp.GE
            elif islt is True:
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:
                    #print(val1, '<=', val2)
                    expr = EM.Le(val1, val2)
                    pred = Cmp.LE

            if expr and not expr.isConstant():
                assert pred
                yield AssertAnnotation(expr, get_subs(state), EM)

def get_safe_inv_candidates(safe, unsafe):
    for s in safe:
        # get and filter out those relations that make the state safe
        saferels = (
            r for r in get_relations(s) if not all(
                u.is_sat(r.getExpr()) for u in unsafe))
        for x in saferels:
            yield x

def get_unsafe_inv_candidates(unsafe):
    for s in unsafe:
        # get and filter out those relations that make the state safe
        EM = s.getExprManager()
        for r in get_relations(s):
            yield r.Not(EM)

def get_safe_relations(states):
    errs = states.errors
    ready = states.ready
    if ready and errs:
        for r in get_safe_inv_candidates(ready, errs):
            yield r
   #if errs:
   #    for r in get_unsafe_inv_candidates(errs):
   #        yield r
    if states.other:
        for r in get_safe_inv_candidates((s for s in states.other if s.isTerminated()), errs):
            yield r

def check_inv(prog, loc, inv, maxk=8):
    dbg_sec(
        f"Checking if {inv} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    apath = AnnotatedCFGPath([loc])
    apath.addLocAnnotationBefore(inv, loc)

    dbg_sec("Running nested KindSE")
    res = kindse.run([apath], maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0

class SimpleInvariantGenerator:
    """
    Generator of invariants for one location in program
    """

    def __init__(self, prog, loc):
        self.program = prog
        self.loc = loc
        self.locid = loc.getBBlock().getID()
        self.tested_invs = {}

    def generate(self, states):
        loc = self.loc
        locid = self.locid
        program = self.program

        for inv in get_safe_relations(states):
            if inv in self.tested_invs.setdefault(locid, set()):
                continue
            self.tested_invs[locid].add(inv)

            print_stdout(f'Checking if {inv} is invariant for {locid}')
            if check_inv(program, loc, inv):
                print_stdout(
                    f"{inv} is invariant of loc {locid}!",
                    color="BLUE")
                yield inv

def check_loop_inv(state, inv):
    EM = state.getExprManager()
    expr = inv.getExpr()
    subs = inv.getSubstitutions()
    for x in (l for l in state.getNondets() if l.isNondetLoad()):
        sval = subs.get(x.load)
        if sval:
            expr = EM.substitute(expr, (sval, x))

    print(inv)
    state.dump()
    print('assume', expr)
    print('assert not', inv.doSubs(state))
    print(state.getConstraints())

    r = state.is_sat(EM.Not(inv.doSubs(state)), expr)
    print(r)
    if r is False:
        # invariant
        return True

    return False

class InvariantGenerator:
    """
    Generator of invariants for one location in program
    """

    def __init__(self, prog, loc):
        self.program = prog
        self.loc = loc
        self.locid = loc.getBBlock().getID()
        self.tested_invs = {}
        self.states = []
        self.relations = []
        # a pair (loop, states after executing the loop body)
        self.loops = {}

        def reportfn(msg, *args, **kwargs):
            print_stdout(f"> {msg}", *args, **kwargs)

        kindse = BaseKindSE(prog)
        kindse.reportfn = reportfn

        self.executor = kindse

    def getLoop(self, loc):
        x = self.loops.get(loc)
        if x:
            return x

        dbg_sec(f"Gathering paths for loc {loc.getBBlock().getID()}")
        L = SimpleLoop.construct(loc)
        if L is None:
            return None
       #S = []
        S = None

       #executor = self.executor
       #for p in L.getPaths():
       #    dbg(f"Got {p}, generating states")
       #    r = executor.executePath(p)
       #    S += r.ready or []

        self.loops[loc] = (L, S)
        dbg_sec()
        return self.loops.get(loc)

    def candidates(self, inv, states):
        print_stdout(f"Generating invariant from {inv}", color="BROWN")
        loc = self.loc
        L, S = self.getLoop(loc)

        executor = self.executor
        ready, unsafe = [], []
        for p in L.getPaths():
            path = p.copy()
            path.addLocAnnotationBefore(inv, loc)
            r = executor.executePath(path)
            if r.ready and not r.errors:
                print_stdout(f"{inv} safe along {p}", color="RED")
            elif r.errors:
                print_stdout(f"{inv} unsafe along {p}", color="RED")
                for e in r.errors:
                    print(e.getConstraints())

            ready += r.ready or []
            unsafe += r.errors or []

        if not unsafe:
            yield inv

    def generate(self, states):
        loc = self.loc
        locid = self.locid
        program = self.program

        #self.states.append(states)

        for rel in get_safe_relations(states):
            if rel in self.tested_invs.setdefault(locid, set()):
                continue
            self.tested_invs[locid].add(rel)

            for inv in self.candidates(rel, states):
                print_stdout(f'Checking if {inv} is invariant for {locid}')
                if check_inv(program, loc, inv):
                    print_stdout(
                        f"{inv} is invariant of loc {locid}!",
                        color="BLUE")
                    yield inv

