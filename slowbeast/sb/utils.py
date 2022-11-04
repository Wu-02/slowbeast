from os.path import join as pathjoin, basename
from subprocess import run
from sys import exit as sys_exit

from slowbeast.util.debugging import dbg, print_stderr


def err(msg):
    print_stderr(msg, color="RED")
    sys_exit(1)


def _run(cmd):
    dbg("RUN: {0}".format(" ".join(cmd)))

    cp = run(cmd)
    if cp.returncode != 0:
        err("Failed running: {0}".format(" ".join(cmd)))


def add_clam_invariants(path, outp=None):
    dbg("Running clam on {0}".format(path))

    if outp is None:
        outp = pathjoin("/tmp/", basename(path) + ".bc")

    cmd = [
        "clam.py",
        "--crab-opt=add-invariants",
        "--crab-opt-invariants-loc=loop-header",
        "--crab-print-invariants=false",
        "-o",
        outp,
        path,
    ]
    _run(cmd)
    dbg("Instrumented to {0}".format(outp))

    return outp


def opt(path, opts=None, outp=None, outd="/tmp/"):
    dbg("Optimizing {0}".format(path))

    if outp is None:
        outp = pathjoin(outd, "optcode.bc")

    cmd = ["opt", "-o", outp, path] + (opts or [])
    _run(cmd)

    dbg("Optimized files to {0}".format(outp))

    return outp
