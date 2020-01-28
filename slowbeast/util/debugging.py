import sys

_is_debugging = False

def set_debugging():
    global _is_debugging
    _is_debugging = True

def dbg(msg):
    if not _is_debugging:
        return

    sys.stderr.write("[sb] ")
    sys.stderr.write(msg)
    sys.stderr.write("\n")
