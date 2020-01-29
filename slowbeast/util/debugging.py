import sys

COLORS = {
    'DARK_BLUE': '\033[0;34m',
    'CYAN': '\033[0;36m',
    'BLUE': '\033[1;34m',
    'PURPLE': '\033[0;35m',
    'RED': '\033[1;31m',
    'GREEN': '\033[1;32m',
    'BROWN': '\033[0;33m',
    'YELLOW': '\033[1;33m',
    'WHITE': '\033[1;37m',
    'GRAY': '\033[0;37m',
    'DARK_GRAY': '\033[1;30m',
    'RESET': '\033[0m'
}


def print_stream(msg, stream, prefix=None, print_nl=True, color=None):
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

    if msg == '':
        return
    if prefix is not None:
        stream.write(prefix)

    stream.write(msg)

    if color is not None:
        stream.write(COLORS['RESET'])

    if print_nl:
        stream.write('\n')

    stream.flush()


def print_stderr(msg, prefix=None, print_nl=True, color=None):
    print_stream(msg, sys.stderr, prefix, print_nl, color)


def print_stdout(msg, prefix=None, print_nl=True, color=None):
    print_stream(msg, sys.stdout, prefix, print_nl, color)


_is_debugging = False


def set_debugging():
    global _is_debugging
    _is_debugging = True


def dbg(msg, print_nl=True, color='GRAY'):
    if not _is_debugging:
        return

    print_stderr(msg, "[sb] ", print_nl, color)
