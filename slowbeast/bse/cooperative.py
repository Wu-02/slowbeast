from slowbeast.domains.concrete import concrete_value
from slowbeast.util.channel import Channel
from .bself import BSELF
from .bselfchecker import BSELFChecker

from .options import BSELFOptions


def concrete_value_from_str(s):
    x, ty = s.split(b":")
    if ty.startswith(b"f"):
        bw = int(ty[1:])
        return concrete_value(float(x), bw)
    if ty == b"bool":
        return concrete_value(bool(x), 1)
    try:
        bw = int(ty[:-1])
        return concrete_value(int(x), bw)
    except ValueError:
        raise NotImplementedError(f"Unhandled value: {s}")


class ReachableState:
    def __init__(self, msg):
        self.msg = msg

        _, loc_s, vals_s = msg.split(b":", 2)
        self.pc = int(loc_s)
        vals_s = vals_s.strip()
        vals = vals_s.split(b",")
        self.values = {
            int(x): concrete_value_from_str(v)
            for x, v in (eq.split(b"=") for eq in vals)
        }

    def __repr__(self):
        return f"ReachableState({self.pc, self.values})"


class CooperativeBSELFChecker(BSELFChecker):
    def __init__(
        self,
        loc,
        A,
        program,
        programstructure,
        opts: BSELFOptions,
        invariants=None,
        indsets=None,
        reachable_states=None,
        max_loop_hits=None,
        channels=None,
    ):
        super().__init__(
            loc,
            A,
            program,
            programstructure,
            opts,
            invariants,
            indsets,
            reachable_states,
            max_loop_hits,
        )
        self.channels = channels

    def create_checker(self, *args, **kwargs):
        return CooperativeBSELFChecker(*args, channels=self.channels, **kwargs)

    def do_step(self):
        ###
        # Channel communication
        ###
        msg = self.channels[0].recv()
        while msg:
            if not msg.startswith(b"reach:"):
                continue

            try:
                state = ReachableState(msg)
            except ValueError:
                state = None
            if state:
                self.reachable_states.setdefault(state.pc, []).append(state)

            msg = self.channels[0].recv()

        return super().do_step()


class CooperativeBSELF(BSELF):
    """
    The main class for BSE and BSELF (BSE is a BSELF without loop folding)
    that divides and conquers the tasks.
    """

    def __init__(
        self, prog, channels, ohandler=None, opts: BSELFOptions = BSELFOptions()
    ) -> None:
        super().__init__(prog, ohandler, opts)
        self.channels = [Channel(chan) for chan in channels]

    def create_checker(self, *args, **kwargs):
        return CooperativeBSELFChecker(*args, channels=self.channels, **kwargs)
