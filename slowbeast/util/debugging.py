import sys

COLORS = {
    "DARK_BLUE": "\033[0;34m",
    "DARK_GREEN": "\033[0;32m",
    "CYAN": "\033[0;36m",
    "BLUE": "\033[1;34m",
    "PURPLE": "\033[0;35m",
    "RED": "\033[1;31m",
    "WINE": "\033[0;31m",
    "GREEN": "\033[1;32m",
    "BROWN": "\033[0;33m",
    "YELLOW": "\033[1;33m",
    "WHITE": "\033[1;37m",
    "GRAY": "\033[0;37m",
    "DARK_GRAY": "\033[1;30m",
    "DARK_GRAY_THIN": "\033[38;5;238m",
    "ORANGE": "\033[38;5;214m",
    "RESET": "\033[0m",
}


def print_stream(msg, stream, prefix=None, print_ws="\n", color=None):
    """
    Print message to stderr/stdout

    @ msg      : str    message to print
    @ prefix   : str    prefix for the message
    @ print_nl : bool  print new line after the message
    @ color    : str    color to use when printing, default None
    """

    # don't print color when the output is redirected
    # to a file
    if not stream.isatty():
        color = None

    if color is not None:
        stream.write(COLORS[color])

    if msg == "":
        return
    if prefix is not None:
        stream.write(prefix)

    stream.write(msg)

    if color is not None:
        stream.write(COLORS["RESET"])

    if print_ws:
        stream.write(print_ws)

    stream.flush()


def print_stderr(msg, prefix=None, print_ws="\n", color=None):
    print_stream(msg, sys.stderr, prefix, print_ws, color)


def print_stdout(msg, prefix=None, print_ws="\n", color=None):
    print_stream(msg, sys.stdout, prefix, print_ws, color)


def print_highlight(s, words, prefix=None, stream=sys.stdout):
    """ Words: dictionary words -> colors """
    if prefix:
        print_stream(prefix, print_ws=None, stream=stream)
    for w in s.split():
        c = words.get(w)
        if c:
            print_stream(w, color=c, print_ws=" ", stream=stream)
        else:
            print_stream(w, print_ws=" ", stream=stream)
    stream.write("\n")


_is_debugging = 0
_debugging_prefix = ""


def set_debugging(verbose=False):
    global _is_debugging
    _is_debugging = 2 if verbose else 1


def unset_debugging():
    global _is_debugging
    _is_debugging = 0


def set_debugging_prefix(prefix=""):
    global _debugging_prefix
    _debugging_prefix = prefix


def get_debugging_prefix():
    global _debugging_prefix
    return _debugging_prefix


def inc_debugging_lvl():
    global _debugging_prefix
    _debugging_prefix = "  " + _debugging_prefix


def dec_debugging_lvl():
    global _debugging_prefix
    if _debugging_prefix.startswith("  "):
        _debugging_prefix = _debugging_prefix[2:]


def dbg_sec(msg=None, color="WHITE"):
    if msg is None:
        dec_debugging_lvl()
    else:
        dbg(msg, color=color)
        inc_debugging_lvl()


def dbg(msg, print_ws="\n", color="GRAY", fn=print_stderr):
    if _is_debugging < 1:
        return

    fn(msg, f"[sb] {_debugging_prefix}", print_ws, color)


def dbgv(msg, print_ws="\n", color="GRAY", fn=print_stderr):
    if _is_debugging < 2:
        return

    fn(msg, f"[sb] {_debugging_prefix}", print_ws, color)


def warn(msg, print_ws="\n", color="BROWN"):
    print_stderr(msg, "[sb] WARNING: ", print_ws, color)


def FIXME(msg, print_ws="\n", color="DARK_GRAY_THIN"):
    print_stderr(msg, "[sb] !FIXME! ", print_ws, color)
