from slowbeast.ir.instruction import Cmp, Load, Assume, Assert
from slowbeast.symexe.pathexecutor import AssertAnnotation
from slowbeast.core.executor import PathExecutionResult

from slowbeast.util.debugging import print_stderr, print_stdout, dbg, dbg_sec
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath

from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . paths import SimpleLoop

# we want our annotations to talk about memory
# and if they talk about the same memory, to look the same
# So for every load X, we create a unique load X that we use
# instead. In other words, we map all the x1 = load X,
# x2 = load X, x3 = load X, ... to one x = load X
cannonic_loads = {}

def get_subs(state):
    global cannonic_loads
    subs = {}
    for l in state.getNondetLoads():
        alloc = l.load.getPointerOperand()
        load = cannonic_loads.setdefault(alloc, Load(alloc, alloc.getSize().getValue()))
        subs[l] = load

    return subs

def get_all_relations(state):
    rels = []
    subs = get_subs(state)
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
            if islt is False:  # val1 >= val2
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:  # val1 <= val2
                    #print(val1, '=', val2)
                    # to avoid generating x = y and y = x as different
                    # expressions
                    if str(val1) < str(val2):
                        expr = EM.Eq(val1, val2)
                    else:
                        expr = EM.Eq(val2, val1)
                elif isgt is True:
                    pass
                    #print(val1, '>=', val2)
                    #expr = EM.Ge(val1, val2)
            elif islt is True:
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:
                    pass
                    #print(val1, '<=', val2)
                    #expr = EM.Le(val1, val2)

            if expr and not expr.isConstant():
                yield AssertAnnotation(expr, subs, EM)

# def get_var_range(state, x):
#     EM = state.getExprManager()
#     Lt = EM.Lt
#     if state.is_sat(Lt(x, EM.Constant(10, x.getBitWidth()))) is False:
#         if state.is_sat(Lt(x, EM.Constant(100, x.getBitWidth()))) is False:
#             if state.is_sat(Lt(x, EM.Constant(1000, x.getBitWidth()))) is False:
#                 lower = 1 << (x.getBitWidth() - 1) - 1 # go to max
#                 upper = None
#             else:
#                 lower = 999
#                 upper = 999
#         else:
#             lower = 99
#             upper = 99
#     else:
#         lower = 9
#         upper = 9

#     trials = 0
#     while trials < 50:
#         rg = state.is_sat(Lt(x, EM.Constant(lower, x.getBitWidth())))
#         if rg is False:
#             break
#         elif rg is None:
#             break

#         upper = lower
#         lower -= int(lower / 2)
#         trials += 1

#     print(f'{lower} <= x <{upper}')
#     return EM.Ge(x, EM.Constant(lower, x.getBitWidth())), Lt(x, EM.Constant(upper, x.getBitWidth()))

def get_safe_relations(safe, unsafe):
    for s in safe:
        # get and filter out those relations that make the state safe
        saferels = (
            r for r in get_all_relations(s))
        for x in saferels:
            yield x

   #for s in unsafe:
   #    # get and filter out those relations that make the state safe
   #    EM = s.getExprManager()
   #    for r in get_all_relations(s):
   #        yield r.Not(EM)

def get_inv_candidates(states):
    errs = states.errors
    ready = states.ready
    yielded = set()
    if ready and errs:
        for r in get_safe_relations(ready, errs):
            if r not in yielded:
                yielded.add(r)
                yield r
    if states.other:
        for r in get_safe_relations((s for s in states.other if s.isTerminated()), errs):
            if r not in yielded:
                yielded.add(r)
                yield r

def check_inv(prog, loc, invs, maxk=8):
    dbg_sec(
        f"Checking if {invs} is invariant of loc {loc.getBBlock().getID()}")

    def reportfn(msg, *args, **kwargs):
        print_stdout(f"> {msg}", *args, **kwargs)

    kindse = BaseKindSE(prog)
    kindse.reportfn = reportfn

    apath = AnnotatedCFGPath([loc])
    for inv in invs:
        apath.addLocAnnotationBefore(inv, loc)

    dbg_sec("Running nested KindSE")
    res = kindse.run([apath], maxk=maxk)
    dbg_sec()
    dbg_sec()
    return res == 0

def annotated_loop_paths(L, pre, post, invs):
    for p in L.getPaths():
        path = p.copy()
        for a in pre:
            path.addPrecondition(a)
        for a in post:
            path.addPostcondition(a)
        for inv in invs:
            path.addLocAnnotationBefore(inv, loc)

        yield path

def exec_on_loop(loc, executor, L, pre=[], post=[], invs=[]):

    def ann(x): return ' & '.join(map(str, x))

    result = PathExecutionResult()
    for path in annotated_loop_paths(L, pre, post, invs):
        r = executor.executePath(path)
        result.merge(r)
       #if r.ready:
       #    print_stdout(f"{ann(invs)} safe along {ann(pre)}{path}{ann(post)}", color="GREEN")
       #if r.errors:
       #    print_stdout(f"{ann(invs)} unsafe along {ann(pre)}{path}{ann(post)}", color="RED")
       #if not r.ready and not r.errors and not r.other:
       #    print_stdout(f"{ann(invs)} infeasible along {ann(pre)}{path}{ann(post)}", color="DARK_GREEN")
        if r.ready:
            print_stdout(f"safe along {path}", color="GREEN")
        if r.errors:
            print_stdout(f"unsafe along {path}", color="RED")
        if not r.ready and not r.errors and not r.other:
            print_stdout(f"infeasible along {path}", color="DARK_GREEN")

    return result

def strengthen(X, A, frames):
    print(X)
    print(A)
    print(frames)

    assert False

abstract = get_inv_candidates
def execute_loop(executor, loc, states):
    dbg_sec(f"Gathering paths for loc {loc.getBBlock().getID()}")
    L = SimpleLoop.construct(loc)
    if L is None:
        return None

    frames = []
    # FIXME: should not be get_inv_candidates, but the pure states
    frames.append(set(abstract(states)))
    print(frames[-1])

    k = 0
    while k < 3:
        r = exec_on_loop(loc, executor, L, post=frames[-1])
        A = set(abstract(r))
        # FIXME: only ready or also safe early and so?
        F = strengthen(r.ready, A, frames)
        if not F:
            F = r.ready

        frames.append(F)

        k += 1

   #executor = self.executor
   #L.states = {}
   #for p in L.getPaths():
   #    dbg(f"Got {p}, generating states")
   #    r = executor.executePath(p)
   #    assert len(r.ready) == 1
   #    assert not r.errors
   #    L.states[p] = r.ready[0]
   #    r.ready[0].dump()

   #self.loops[loc] = L
    dbg_sec()
    assert False, "FINISHED exec loop"

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
        self.abstract_path = []
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

       #executor = self.executor
       #L.states = {}
       #for p in L.getPaths():
       #    dbg(f"Got {p}, generating states")
       #    r = executor.executePath(p)
       #    assert len(r.ready) == 1
       #    assert not r.errors
       #    L.states[p] = r.ready[0]
       #    r.ready[0].dump()

        self.loops[loc] = L
        dbg_sec()
        return self.loops.get(loc)

    def runOnLoop(self, L, pre=[], post=[], invs=[]):
        loc = L.loc
        executor = self.executor

        def ann(x): return ' & '.join(map(str, x))

        result = PathExecutionResult()
        for path in annotated_loop_paths(L, pre, post, invs):
            r = executor.executePath(path)
            result.merge(r)
            if r.ready:
                print_stdout(f"{ann(invs)} safe along {ann(pre)}{path}{ann(post)}", color="GREEN")
            if r.errors:
                print_stdout(f"{ann(invs)} unsafe along {ann(pre)}{path}{ann(post)}", color="RED")
            if not r.ready and not r.errors and not r.other:
                print_stdout(f"{ann(invs)} infeasible along {ann(pre)}{path}{ann(post)}", color="DARK_GREEN")

        return result

    def strengthen(self, L, invs, ready, unsafe):
        if not ready:
            return
        assert unsafe

        L.computeMonotonicVars(self.executor)
        V = L.vars
        for (v, m) in V.items():
            if m == '<' or m == '<=': # monotonic variable
                for s in unsafe:
                    EM = s.getExprManager()
                    x = s.getNondetLoadOf(v)
                    assert x

                    c = s.concretize(x)[0]
                    lt = EM.Lt(c, x)
                    yield invs + [AssertAnnotation(lt, invs[0].getSubstitutions(), EM)]

    def update_abstract_path(self):
        relations = self.relations
        assert relations
        print('RELS', relations[-1])

        if len(relations) < 2:
            self.abstract_path.append(relations[-1])
            return

        R = relations[-1].intersection(relations[-2])
        if R:
            self.abstract_path[-1] = R
        else:
            self.abstract_path.append(relations[-1])

        print(self.abstract_path)

    def generate(self, states):
        loc = self.loc
        locid = self.locid
        program = self.program

        self.states.append(states)
        self.relations.append(set(get_inv_candidates(states)))

        self.update_abstract_path()
        L = self.getLoop(loc)
        if not L:
            return

        for rel in self.relations[-1]:
            r = self.runOnLoop(L, post=[rel])
            for x in get_inv_candidates(r):
                print(x)
                r2 = self.runOnLoop(L, post=[x])
                print(set(get_inv_candidates(r)))

        assert False


        if False:
            yield []

       #for rel in get_inv_candidates(states):
       #    if rel in self.tested_invs.setdefault(locid, set()):
       #        continue
       #    self.tested_invs[locid].add(rel)

       #    dbg_sec(f"Generating invariant from {rel}", color="BROWN")
       #    L = self.getLoop(self.loc)
       #    if not L:
       #        continue

       #    k = 0
       #    workbag = [[rel]]
       #    newworkbag = []
       #    while workbag:
       #        for invs in workbag:
       #            ready, unsafe = self.checkOnLoop(L, invs)
       #            if not unsafe and ready:
       #                # we have some states (not all paths were killed by invs)
       #                # but none erroneoues -- then this is partial invariant!
       #                print_stdout(f'{invs} is partial invariant for {locid}',
       #                             color='DARK_BLUE')
       #                dbg(f'Checking if {invs} is invariant for {locid}')
       #                # FIXME: check only incomming paths to loop (as it is
       #                # partial invariant now)
       #                if check_inv(program, loc, invs):
       #                    print_stdout(
       #                        f"{invs} is invariant of loc {locid}!",
       #                        color="BLUE")
       #                    yield invs
       #                # FIXME: we can annotate CFG now for forward SE
       #                    break
       #            else:
       #                for newinv in self.strengthen(L, invs, ready, unsafe):
       #                    newworkbag.append(newinv)
       #        workbag = newworkbag
       #    dbg_sec()


            # now it is partial invariant
# class SimpleInvariantGenerator:
#     """
#     Generator of invariants for one location in program
#     """

#     def __init__(self, prog, loc):
#         self.program = prog
#         self.loc = loc
#         self.locid = loc.getBBlock().getID()
#         self.tested_invs = {}

#     def generate(self, states):
#         loc = self.loc
#         locid = self.locid
#         program = self.program

#         for inv in get_inv_candidates(states):
#             if inv in self.tested_invs.setdefault(locid, set()):
#                 continue
#             self.tested_invs[locid].add(inv)

#             print_stdout(f'Checking if {inv} is invariant for {locid}')
#             if check_inv(program, loc, inv):
#                 print_stdout(
#                     f"{inv} is invariant of loc {locid}!",
#                     color="BLUE")
#                 yield inv

# def check_loop_inv(state, inv):
#     EM = state.getExprManager()
#     expr = inv.getExpr()
#     subs = inv.getSubstitutions()
#     for x in (l for l in state.getNondets() if l.isNondetLoad()):
#         sval = subs.get(x.load)
#         if sval:
#             expr = EM.substitute(expr, (sval, x))

#     print(inv)
#     state.dump()
#     print('assume', expr)
#     print('assert not', inv.doSubs(state))
#     print(state.getConstraints())

#     r = state.is_sat(EM.Not(inv.doSubs(state)), expr)
#     print(r)
#     if r is False:
#         # invariant
#         return True

#     return False


