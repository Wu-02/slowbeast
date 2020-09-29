from slowbeast.ir.instruction import Cmp, Load, Assume, Assert
from slowbeast.symexe.pathexecutor import AssertAnnotation

from slowbeast.util.debugging import print_stderr, print_stdout, dbg, dbg_sec
from slowbeast.kindse.annotatedcfg import AnnotatedCFGPath

from . kindsebase import KindSymbolicExecutor as BaseKindSE
from . paths import SimpleLoop

def get_subs(state):
    return {l.load : l for l in (n for n in state.getNondets() if n.isNondetLoad())}

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
                    #expr = EM.Ge(val1, val2)
                    pred = Cmp.GE
            elif islt is True:
                gt = EM.Gt(val1, val2)
                isgt = state.is_sat(gt)
                if isgt is False:
                    #print(val1, '<=', val2)
                    #expr = EM.Le(val1, val2)
                    pred = Cmp.LE

            if expr and not expr.isConstant():
                assert pred
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
    if ready and errs:
        for r in get_safe_relations(ready, errs):
            yield r
    if states.other:
        for r in get_safe_relations((s for s in states.other if s.isTerminated()), errs):
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

        executor = self.executor
       #S = []
       #for p in L.getPaths():
       #    dbg(f"Got {p}, generating states")
       #    r = executor.executePath(p)
       #    S += r.ready or []

        # FIXME: we may want to do this after adding annotations
        # (we then may get more results)

        self.loops[loc] = L
        dbg_sec()
        return self.loops.get(loc)

    def checkOnLoop(self, L, invs):
        loc = L.loc
        executor = self.executor
        ready, unsafe = [], []
        for p in L.getPaths():
            path = p.copy()
            for inv in invs:
                path.addLocAnnotationBefore(inv, loc)

            r = executor.executePath(path)
            if r.ready and not r.errors:
                print_stdout(f"{' & '.join(map(str, invs))} safe along {p}", color="GREEN")
            elif r.errors:
                print_stdout(f"{' & '.join(map(str, invs))} unsafe along {p}", color="RED")
            else:
                print_stdout(f"{' & '.join(map(str, invs))} infeasible along {p}", color="BLUE")

            ready += r.ready or []
            unsafe += r.errors or []
        return ready, unsafe

    def strengthen(self, L, invs, ready, unsafe):
        #L.computeMonotonicVars(self.executor)
        return invs

    def generate(self, states):
        loc = self.loc
        locid = self.locid
        program = self.program

        #self.states.append(states)

        for rel in get_inv_candidates(states):
            if rel in self.tested_invs.setdefault(locid, set()):
                continue
            self.tested_invs[locid].add(rel)

            dbg_sec(f"Generating invariant from {rel}", color="BROWN")
            L = self.getLoop(self.loc)
            if not L:
                continue

            k = 0
            invs = [rel]
            while k < 10:
                ready, unsafe = self.checkOnLoop(L, invs)
                if not unsafe:
                    dbg(f'Checking if {invs} is invariant for {locid}')
                    # FIXME: check only incomming paths to loop (as it is
                    # partial invariant now)
                    if check_inv(program, loc, invs):
                        print_stdout(
                            f"{invs} is invariant of loc {locid}!",
                            color="BLUE")
                        yield invs
                        break

                invs = self.strengthen(L, invs, ready, unsafe)
                k += 1
            dbg_sec()


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


