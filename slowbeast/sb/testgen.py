from os.path import join as pathjoin

from slowbeast.domains.symbolic_helpers import to_c_expression
from slowbeast.ir.instruction import Call


def _inv_to_c(inv):
    return f"({to_c_expression(inv.get_cannonical().unwrap())})"


def inv_to_c(inv):
    return str(" && ".join(map(_inv_to_c, inv)))


class TestCaseGenerator:
    def __init__(
        self,
        args,
        only_tests=None,
        checking=None,
    ):
        self._args = args
        self._outputdir = args.out_dir or "sb-out"
        self._alltests = args.all_tests
        self._svcomp_witness = args.svcomp_witness
        self._only_tests = only_tests
        self._checking = checking

    def _openfile(self, path):
        return open(pathjoin(self._outputdir, path), "w")

    def process_error_state(self, fl, state):
        fl.write(state.get_error().descr())
        fl.write("\n")
        fl.write("\n")
        fl.write("Nondeterministic values:\n")
        inpvec = state.input_vector()
        if inpvec is None:
            raise RuntimeError("No input vector, formula is UNSAT?")
        for var, val in zip(state.nondets(), inpvec):
            # dump as unsigned and signed
            fl.write(f"  {var} -> {val.value()}u")
            fl.write(
                " ({0})\n".format(
                    val.value()
                    if val.value() < (1 << (val.bitwidth() - 1))
                    else (val.value() - (1 << val.bitwidth()))
                )
            )
        fl.write("\n")
        state.dump(stream=fl)

    # FIXME: move out of testgen (it is not generating tests...)
    def generate_proof(self, executor):
        invariants = executor.invariants
        with self._openfile(f"invariants.txt") as fl:
            write = fl.write
            for loc, inv in invariants.items():
                dbgloc = None
                bblock = loc.elem()
                for inst in bblock:
                    dbgloc = inst.get_metadata("dbgloc")
                    if dbgloc:
                        break
                if dbgloc:
                    write(f"{dbgloc[0]}:{dbgloc[1]}:{dbgloc[2]} {inv_to_c(inv)}\n")
                else:
                    write(f"{loc}: {inv_to_c(inv)}\n")
        if self._svcomp_witness:
            with self._openfile(f"correctness-witness.graphml") as fl:
                self.generate_svcomp_correctness_witness(fl, invariants)

    def _svcomp_header(self, fl):
        write = fl.write
        write("<?xml version='1.0' encoding='UTF-8'?>\n")
        write(
            '<graphml xmlns="http://graphml.graphdrawing.org/xmlns" '
            'xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance">\n'
        )
        write('<graph edgedefault="directed">\n\n')
        write('<node id="0">\n')
        write('  <data key="entry">true</data>\n')
        write("</node>\n\n")

    def _svcomp_footer(self, fl):
        write = fl.write
        write("</graph>\n")
        write("</graphml>\n")

    def generate_svcomp_violation_witness(self, fl, state):
        inpvec = state.input_vector()
        if inpvec is None:
            raise RuntimeError("No input vector, formula is UNSAT?")
        write = fl.write
        self._svcomp_header(fl)

        lid = 0
        for var, val in zip(state.nondets(), inpvec):
            instruction = var.instruction
            if not isinstance(instruction, Call):
                print("Unhandled nondet value: ", var)
                continue
            var = instruction.called_function().name()

            lid += 1
            # dump as unsigned and signed
            write(f'<node id="{lid}"/>\n')
            write(f'<edge source="{lid-1}" target="{lid}">\n')
            write(f'  <data key="assumption">\\result=={val.value()}</data>\n')
            write(f'  <data key="assumption.resultfunction">{var}</data>\n')
            bblock = instruction.bblock()
            for inst in bblock:
                dbgloc = inst.get_metadata("dbgloc")
                if dbgloc:
                    write(f'  <data key="startline">{dbgloc[1]}</data>\n')
                    break
            write("</edge>\n")
        write(f'<node id="{lid+1}">\n')
        if self._checking and (
            "termination" in self._checking or "non-termination" in self._checking
        ):
            write('  <data key="cyclehead">true</data>\n')
        else:
            write('  <data key="violation">true</data>\n')
        write("</node>\n\n")
        write(f'<edge source="{lid}" target="{lid+1}"/>\n')
        self._svcomp_footer(fl)

    def generate_svcomp_correctness_witness(self, fl, invariants):
        write = fl.write
        self._svcomp_header(fl)
        lid = 0
        for loc, inv in invariants.items():
            lid += 1
            # dump as unsigned and signed
            write(f'<node id="{lid}">\n')
            cinv = inv_to_c(inv)
            cinv = cinv.replace("&&", "&amp;&amp;")
            cinv = cinv.replace("<", "&lt;")
            cinv = cinv.replace(">", "&gt;")
            write(f'  <data key="invariant">{cinv}</data>\n')
            write(f"</node>\n")
            # write(f'<edge source="{lid-1}" target="{lid}">\n')
            write(f'<edge source="{0}" target="{lid}">\n')
            bblock = loc.elem()
            for inst in bblock:
                dbgloc = inst.get_metadata("dbgloc")
                if dbgloc:
                    write(f'  <data key="startline">{dbgloc[1]}</data>\n')
                    break
            write("</edge>\n")

        self._svcomp_footer(fl)

    def process_state(self, state):
        assert not state.is_ready(), state

        if not self._alltests and state.exited():
            return

        testty = None
        if state.has_error():
            testty = "err"
        elif state.is_killed():
            testty = "killed"
        elif state.is_terminated():
            testty = "abort"
        else:
            testty = "exited"

        if self._only_tests and testty not in self._only_tests:
            return

        filename = f"{state.get_id()}.{testty}.test"

        with self._openfile(filename) as fl:
            fl.write(str(state.status()))
            fl.write("\n")
            if state.has_error():
                self.process_error_state(fl, state)
            else:
                fl.write("\n")
                state.dump(stream=fl)

        if state.has_error():
            if self._svcomp_witness:
                with self._openfile(f"witness-{state.get_id()}.graphml") as fl:
                    self.generate_svcomp_violation_witness(fl, state)
            if self._args.gen_harness:
                with self._openfile(f"harness-{state.get_id()}.c") as fl:
                    self.generate_c_harness(fl, state)

    def generate_c_harness(self, fl, state):
        inpvec = state.input_vector()
        if inpvec is None:
            raise RuntimeError("No input vector, formula is UNSAT?")
        write = fl.write

        write("#include <assert.h>\n\n")

        funs = {}
        # group inputs into sequences per functions
        for var, val in zip(state.nondets(), inpvec):
            instruction = var.instruction
            if not isinstance(instruction, Call):
                print("Unhandled nondet value: ", var)
                continue
            fun = instruction.called_function()
            funs.setdefault(fun, []).append(val)

        for fun, vals in funs.items():
            self._function_decl(write, fun)
            write(" {\n")

            write("  static unsigned counter = 0;\n")
            write("  switch (counter++) {\n")
            for n, val in enumerate(vals):
                write(f"    case {n}: return {val.value()};\n")

            write("    default: return 0;\n")
            write("  }\n")
            write("}\n\n")

    def _function_decl(self, write, fun):
        args = ", ".join(f"{c_type(a.type())} a_{n}" for n, a in enumerate(fun.arguments())) or "void"
        write(f"{c_type(fun.return_type())} {fun.name()}({args})")

def c_type(ty):
    if ty.is_bv():
        # FIXME: use layout
        if ty.bitwidth() == 8: return 'unsigned char'
        if ty.bitwidth() == 16: return 'unsigned short'
        if ty.bitwidth() == 32: return 'unsigned int'
        if ty.bitwidth() == 64: return 'unsigned long int'
    if ty.is_float():
        if ty.bitwidth() == 32: return 'float'
        if ty.bitwidth() == 64: return 'double'
    if ty.is_bool():
        return "_Bool"

    return "void"


class ThreadedTestCaseGenerator(TestCaseGenerator):
    def generate_svcomp_violation_witness(self, fl, state):
        inpvec = state.input_vector()
        write = fl.write
        self._svcomp_header(fl)

        lid = 0
        for tid, pc in state.trace():
            print(tid, pc)

            lid += 1
            # dump as unsigned and signed
            write(f'<node id="{lid}"/>\n')
            write(f'<edge source="{lid-1}" target="{lid}">\n')
            write(f'  <data key="threadId">{tid}</data>\n')
            bblock = pc.bblock()
            for inst in bblock:
                dbgloc = inst.get_metadata("dbgloc")
                if dbgloc:
                    write(f'  <data key="startline">{dbgloc[1]}</data>\n')
                    break
            write("</edge>\n")
        write(f'<node id="{lid+1}">\n')
        write('  <data key="violation">true</data>\n')
        write("</node>\n\n")
        write(f'<edge source="{lid}" target="{lid+1}"/>\n')
        self._svcomp_footer(fl)
