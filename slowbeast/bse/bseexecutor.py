from slowbeast.symexe.pathexecutor import Executor as PathExecutor
from slowbeast.symexe.executionstate import LazySEState
from slowbeast.symexe.annotations import ExprAnnotation, execute_annotation
from slowbeast.domains.pointer import Pointer
from slowbeast.util.debugging import ldbgv
from .memorymodel import _nondet_value

def _substitute_unknown_ptrs(substitute, subs, M):
    """
    Returns substituted version of unknown_ptrs and a list of equalities that
    must be satisfited.
    """
    # FIXME: more efficient way?
    newM = {}
    eqs = []
    for p, x in M.items():
        ptr = Pointer(substitute(p.object(), *subs), substitute(p.offset(), *subs))
        val = Pointer(substitute(x.object(), *subs), substitute(x.offset(), *subs))\
              if x.is_pointer()\
              else substitute(x, *subs)
        oldval = M.get(ptr)
        if oldval and (type(oldval) is not type(val) or oldval != val):
            eqs.append((oldval, val))
        newM[ptr] = val
    return newM, eqs

def _break_ptr_substitutions(subs):
    for o, n in subs:
        yield (o.object(), n.object())
        yield (o.offset(), n.offset())

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

    def apply_postcondition(self, postcondition):
        if isinstance(postcondition, BSEState):
            return self._apply_postcondition_state(postcondition)
        if isinstance(postcondition, ExprAnnotation):
            good, _ = execute_annotation(self.executor(), [self], postcondition)
            return good
        raise NotImplementedError(f"Invalid post-condition: {postcondition}")

    def _apply_postcondition_state(self, poststate):
        print('-- Applying post')
        print("State:", self)
        print('-- --')
        print("Post-state:", poststate)
        print('-- -- --')
        ###
        # apply postcondition to constraints
        add_constr = self.addConstraint
        em = self.expr_manager()
        substitute = em.substitute

        ptr_subs, subs = self._get_inputs_substitutions(poststate.nondets())

        M = self.memory
        aM = poststate.memory
        pUP = aM._unknown_ptrs
        if ptr_subs:
            print('pointer subs')
            all_ptr_subs = ptr_subs
            while ptr_subs:
                new_ptr_subs = []
                for oldptr, newptr in ptr_subs:
                    print(oldptr, '->', newptr)
                    print('NPTR', type(newptr.object()), type(newptr.offset()))
                    # do we have loads from these pointers?
                    load_optr = pUP.get(oldptr)
                    if load_optr:
                        load_nptr, _ = M.read(newptr, load_optr.bytewidth())
                        if load_nptr:
                            if load_nptr.is_pointer():
                                assert load_optr.is_pointer()
                                print('new', load_optr, '->', load_nptr)
                                new_ptr_subs.append((load_optr, load_nptr))
                            else:
                                subs.append((load_optr, load_nptr))
                all_ptr_subs += new_ptr_subs
                ptr_subs = new_ptr_subs
            ptr_subs = list(_break_ptr_substitutions(all_ptr_subs))

        print('PTR SUBS', ptr_subs)

        changed = True
        while changed:
            changed = False
            for ptr, val in pUP.items():
                if ptr_subs:
                    ptr = Pointer(substitute(ptr.object(), *ptr_subs, *subs), substitute(ptr.offset(), *ptr_subs, *subs))
                    val = Pointer(substitute(val.object(), *ptr_subs, *subs), substitute(val.offset(), *ptr_subs, *subs)) \
                        if val.is_pointer() else substitute(val, *ptr_subs, *subs)
                    print('PTR', ptr)
                    print(type(ptr.object()), type(ptr.offset()))
                    newval, _ = M.read(ptr, val.bytewidth())
                    if newval and (type(newval) is not type(val) or newval != val):
                        subs.append((val, newval))
                        changed = True

                # FIXME do not touch protected members...
                if hasattr(M, '_unknown_ptrs'):
                    M._unknown_ptrs[ptr] = val

        print(subs)
        add_pc = poststate.path_condition()
        add_constr(substitute(add_pc, *subs))

        print("Pre-state:", self)
        print('-- Applying post finished')
        if self.isfeasible():
            return [self]
        return []

    def _get_inputs_substitutions(self, inputs):
        try_eval = self.try_eval
        add_input = self.add_nondet
        ptr_subs = []
        subs = []
        for inp in inputs:
            val = try_eval(inp.instruction)
            if val:
                print('HIT INP', inp.instruction, val)
                oldvalue = inp.value
                if oldvalue.is_pointer():
                    assert val.is_pointer(), val
                    ptr_subs.append((oldvalue, val))
                else:
                    assert not oldvalue.is_pointer()
                    assert not val.is_pointer()
                    subs.append((oldvalue, val))
            else:
                # unmatched, we must propagate it further
                add_input(inp)
        return ptr_subs, subs

    def __repr__(self):
        s = f"{self.getConstraints()}\n"
        if hasattr(self.memory, '_unknown_ptrs'):
            s += "\n".join(f"L({p.as_value()})={x}" for p, x in self.memory._unknown_ptrs.items())
        else:
            s += 'CoreMEM'
        s += "\n"+"\n".join(f"{nd.instruction.as_value()}={nd.value}" for nd in self._nondets)
        return s

class Executor(PathExecutor):
    """
    Symbolic Executor instance adjusted to executing
    CFA paths possibly annotated with formulas.
    """

    def __init__(self, solver, opts, memorymodel=None):
        super().__init__(solver, opts, memorymodel)

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

