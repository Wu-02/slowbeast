from slowbeast.bse.bse import report_state
from slowbeast.bse.bself import BSELF, BSELFOptions, BSELFChecker
from slowbeast.cfkind.naive.naivekindse import Result
from slowbeast.util.debugging import print_stdout


class BSELFF(BSELF):
    """
    The main class for BSELFF (BSELF with forward analysis)
    """

    def __init__(self, prog, ohandler=None, opts=BSELFOptions()):
        super().__init__(prog, ohandler, opts)
        self.forward_states = {}

    def run(self):
        has_unknown = False
        bself_checkers = []
        for loc, A in self._get_possible_errors():
            print_stdout(f"Checking possible error: {A.expr()} @ {loc}", color="white")
            checker = BSELFChecker(
                loc,
                A,
                self.program,
                self.programstructure,
                self.options,
                invariants=self.invariants,
            )
            bself_checkers.append(checker)

        for checker in bself_checkers:
            result, states = checker.check()
            self.stats.add(checker.stats)
            if result is Result.UNSAFE:
                # FIXME: report the error from bsecontext
                print_stdout(
                    f"{states.get_id()}: [assertion error]: {loc} reachable.",
                    color="redul",
                )
                print_stdout(str(states), color="wine")
                print_stdout("Error found.", color="redul")
                self.stats.errors += 1
                return result
            if result is Result.SAFE:
                print_stdout(
                    f"Error condition {A.expr()} at {loc} is safe!.", color="green"
                )
            elif result is Result.UNKNOWN:
                print_stdout(f"Checking {A} at {loc} was unsuccessful.", color="yellow")
                has_unknown = True
                assert checker.problematic_states, "Unknown with no problematic paths?"
                for p in checker.problematic_states:
                    report_state(self.stats, p)

        if has_unknown:
            print_stdout("Failed deciding the result.", color="orangeul")
            return Result.UNKNOWN

        print_stdout("No error found.", color="greenul")
        ohandler = self.ohandler
        if ohandler:
            ohandler.testgen.generate_proof(self)
        return Result.SAFE