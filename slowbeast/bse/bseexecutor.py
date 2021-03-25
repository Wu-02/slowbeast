from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.executionstate import LazySEState
from slowbeast.symexe.annotations import ExprAnnotation, execute_annotation
from slowbeast.domains.pointer import Pointer
from slowbeast.domains.concrete import ConcreteInt
from slowbeast.ir.instruction import Load
from slowbeast.util.debugging import ldbgv
from .memorymodel import BSEMemoryModel, _nondet_value

def _subst_val(substitute, val, subs):
    assert isinstance(subs, tuple), subs
    assert len(subs) == 2, subs
    if subs[0].is_pointer():
        assert subs[1].is_pointer(), subs
        subs = ((subs[0].object(), subs[1].object()),
                (subs[0].offset(), subs[1].offset()))
    else:
        assert not subs[1].is_pointer(), subs
        subs = (subs,)
    if val.is_pointer():
        return Pointer(substitute(val.object(), *subs),
                       substitute(val.offset(), *subs))
    return substitute(val, *subs)

class BSEState(LazySEState):
    def __init__(self, executor, pc, m, solver, constraints=None):
        super().__init__(executor, pc, m, solver, constraints)

    def eval(self, v):
        value = self.try_eval(v)
        if value is None:
            value = _nondet_value(self.solver().fresh_value, v, v.type().bitwidth())
            ldbgv(
                "Created new nondet value {0} = {1}",
                (v.as_value(), value),
                color="dark_blue",
            )
            self.set(v, value)
            self.create_nondet(v, value)
        return value

    def memory_constraints(self):
        M = self.memory._reads
        em = self.expr_manager()
        Eq, And, Or, Not = em.Eq, em.And, em.Or, em.Not
        reads = list(M.items())
        constraints = []
        for idx1 in range(0, len(reads)):
            ptr1, val1 = reads[idx1]
            for idx2 in range(idx1 + 1, len(reads)):
                ptr2, val2 = reads[idx2]
                if val1 is val2 or val1.bitwidth() != val2.bitwidth():
                    continue
                # if the pointers are the same, the values must be the same
                c = Or(Not(And(Eq(ptr1.object(), ptr2.object()), Eq(ptr1.offset(), ptr2.offset()))), Eq(val1, val2))
                if c.is_concrete() and bool(c.value()):
                    continue
                constraints.append(c)
        return constraints

    def apply_postcondition(self, postcondition):
        if isinstance(postcondition, ExprAnnotation):
            good, _ = execute_annotation(self.executor(), [self], postcondition)
            return good
        raise NotImplementedError(f"Invalid post-condition: {postcondition}")

    def _replace_value(self, prestate, val, newval):
        em = self.expr_manager()
        #print('REPLACING', val, 'WITH', newval)

        # coerce the values
        if not val.is_bool() and newval.is_bool():
            assert val.bitwidth() == 1, val
            newval = em.Ite(newval, ConcreteInt(1, 1), ConcreteInt(0, 1))
        if not val.is_float() and newval.is_float():
            assert val.bitwidth() == newval.bitwidth()
            newval = em.Cast(newval, val.type())

        assert val.type() == newval.type(), f"{val} -- {newval}"
        # FIXME: use incremental solver
        substitute = em.substitute
        new_repl = []
        pc = self.path_condition()
        if val.is_pointer():
            # if the value is pointer, we must substitute it also in the state of the memory
            assert newval.is_pointer(), newval
            pc = substitute(pc, (val.object(), newval.object()), (val.offset(), newval.offset()))
        else:
            # FIXME: we should replace the value also in memory, shouldn't we?
            pc = substitute(pc, (val, newval))
        self._replace_value_in_memory(new_repl, newval, prestate, substitute, val)
        self.setConstraints(pc)

        return new_repl

    def replace_value(self, prestate, val, newval):
        # recursively handle the implied equalities
        replace_value = self._replace_value
        new_repl = replace_value(prestate, val, newval)
        while new_repl:
            tmp = []
            for r in new_repl:
                tmp += replace_value(prestate, r[0], r[1])
            new_repl = tmp

    def _replace_value_in_memory(self, new_repl, newval, prestate, substitute, val):
        self._replace_final_memory(new_repl, newval, prestate, substitute, val)

    def _replace_final_memory(self, new_repl, newval, prestate, substitute, val):
        UP = self.memory._reads
        nUP = {}
        for cptr, cval in UP.items():
            nptr = _subst_val(substitute, cptr, (val, newval))
            nval = _subst_val(substitute, cval, (val, newval))

            curval = nUP.get(nptr)
            if curval:
                new_repl.append((curval, nval))
            nUP[nptr] = nval

        self.memory._reads = nUP

    def _get_symbols(self):
        symbols = set(s for e in self.getConstraints() for s in e.symbols() if not e.is_concrete())
        for ptr, val in self.memory._reads.items():
            symbols.update(ptr.symbols())
            symbols.update(val.symbols())
        return symbols

    def join_prestate(self, prestate):
        assert isinstance(prestate, BSEState), type(prestate)
       #print('-- Joining with pre-state')
       #print("Pre-state:", prestate)
       #print('-- --')
       #print("State:", self)
       #print('-- -- --')
        ###
        em = self.expr_manager()
        try_eval = prestate.try_eval
        add_input = self.add_nondet

        ### modify the state according to the pre-state
        replace_value = self.replace_value
        for inp in self.nondets():
            instr = inp.instruction
            if isinstance(instr, Load):
                # try read the memory if it is written in the state
                addrop = instr.operand(0)
                addr = try_eval(addrop)
                if addr:
                    val, _ = prestate.memory.read(addr, inp.value.bytewidth())
                    if val:
                        #print('REPL from memory', inp.value, val)
                        replace_value(prestate, inp.value, val)
            else:
                preval = try_eval(inp.instruction)
                if preval:
                    #print('REPL from reg', inp.value, preval)
                    replace_value(prestate, inp.value, preval)

        # filter the inputs that still need to be found
        symbols = set(self._get_symbols())
        self._nondets = [inp for inp in self.nondets() if not symbols.isdisjoint(inp.value.symbols())]
        assert len(self._nondets) <= len(symbols)
        assert len(set(inp.instruction for inp in self._nondets)) == len(self._nondets), "Repeated value for an instruction"

        ### copy the data from pre-state
        # add memory state from pre-state
        # FIXME: do not touch the internal attributes
        for k, v in prestate.memory._reads.items():
            if k not in self.memory._reads:
                self.memory._reads[k] = v
        # add new inputs from pre-state
        for inp in prestate.nondets():
            add_input(inp)
        self.addConstraint(*prestate.getConstraints())

        #print("==Pre+state ==")
        #print(self)
        #print("==============")
        if self.isfeasible():
            return [self]
        return []

    def __repr__(self):
        s = f"pc: {self.getConstraints()}"
        if self.memory._reads:
            s += "\n"+"\n".join(f"+L({p.as_value()})={x}" for p, x in self.memory._reads.items())
        if self._nondets:
            s += "\n"+"\n".join(f"{nd.instruction.as_value()}={nd.value}" for nd in self._nondets)
        return s

class Executor(PathExecutor):
    """
    Symbolic Executor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(self, solver, opts, memorymodel=None):
        super().__init__(solver, opts, memorymodel or BSEMemoryModel(opts))

    def createState(self, pc=None, m=None):
        """
        Overridden method for creating states.
        Since the path may not be initial, we must use states
        that are able to lazily create unknown values
        """
        if m is None:
            m = self.getMemoryModel().createMemory()
        s = BSEState(self, pc, m, self.solver)
        assert not s.getConstraints(), "the state is not clean"
        return s

    def execute_edge(self, states, edge, invariants=None):
        """
        states - pre-condition states (execute from these states)
        """
        assert all(map(lambda s: isinstance(s, LazySEState), states))

        source, target = edge.source(), edge.target()
        ready, nonready = states, []
        # annotations before taking the edge (proably an invariant)
        execannot = self.execute_annotations
        # annotations before source
        locannot = invariants(source) if invariants else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_call() and not edge.called_function().isUndefined():
            fn = edge.called_function().name()
            for s in ready:
                s.setTerminated(f"Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        # annotations before target
        locannot = invariants(target) if invariants else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after target

        return ready, nonready

    def execute_annotated_edge(self, states, edge,
                     pre=None, post=None,
                     annot_before_loc=None, annot_after_loc=None):
        """
        states - pre-condition states (execute from these states)
        """
        assert all(map(lambda s: isinstance(s, LazySEState), states))

        source, target = edge.source(), edge.target()
        ready, nonready = states, []
        # annotations before taking the edge (proably an invariant)
        execannot = self.execute_annotations
        if pre:
            ready, tu = execannot(ready, pre)
            nonready += tu
        # annotations before source
        locannot = annot_before_loc(source) if annot_before_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after source
        locannot = annot_after_loc(source) if annot_after_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu

        # execute the instructions from the edge
        if edge.is_assume():
            ready, tmpnonready = self._exec_assume_edge(ready, edge)
            nonready += tmpnonready
        elif edge.is_call() and not edge.called_function().isUndefined():
            fn = edge.called_function().name()
            for s in ready:
                s.setTerminated(f"Called function {fn} on intraprocedural path")
                return [], nonready + ready
            raise NotImplementedError("Call edges not implemented")
        else:
            ready, tmpnonready = self.execute_seq(ready, edge)
            nonready += tmpnonready

        # annotations before target
        locannot = annot_before_loc(target) if annot_before_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        # annotations after target
        locannot = annot_after_loc(target) if annot_after_loc else None
        if locannot:
            ready, tu = execannot(ready, locannot)
            nonready += tu
        if post:
            ready, tu = execannot(ready, post)
            nonready += tu

        return ready, nonready

