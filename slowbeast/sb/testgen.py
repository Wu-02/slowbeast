from os.path import join as pathjoin

from slowbeast.domains.symbolic_helpers import to_c_expression
from slowbeast.ir.instruction import Call


def _inv_to_c(inv):
    return f"({to_c_expression(inv.get_cannonical().unwrap())})"


def inv_to_c(inv):
    return str(" && ".join(map(_inv_to_c, inv)))


class TestCaseGenerator:
    def __init__(self, outdir="sb-out", alltests=False, svwit=False, only_tests=None):
        self._outputdir = outdir
        self._alltests = alltests
        self._svcomp_witness = svwit
        self._only_tests = only_tests

    def _openfile(self, path):
        return open(pathjoin(self._outputdir, path), "w")

    def process_error_state(self, fl, state):
        fl.write(state.get_error().descr())
        fl.write("\n")
        fl.write("\n")
        fl.write("Nondeterministic values:\n")
        inpvec = state.input_vector()
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
        elif state.was_killed():
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

        if state.has_error() and self._svcomp_witness:
            with self._openfile(f"witness-{state.get_id()}.graphml") as fl:
                self.generate_svcomp_violation_witness(fl, state)


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
