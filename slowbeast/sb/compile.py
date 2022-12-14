from os.path import join as pathjoin, basename

from slowbeast.sb.utils import _run, err
from slowbeast.util.debugging import dbg


def sort_input_files(files):
    c_files = []
    llvm_files = []

    for f in files:
        if f.endswith(".c") or f.endswith(".i"):
            c_files.append(f)
        elif f.endswith(".bc") or f.endswith(".ll"):
            llvm_files.append(f)
        else:
            err("Unknown file: {0}".format(f))

    return c_files, llvm_files


def compile_c(path, outp=None, addargs=None):
    dbg("Compiling {0}".format(path))

    if outp is None:
        outp = pathjoin("/tmp/", basename(path) + ".bc")

    cmd = [
        "clang",
        "-D__inline=",
        "-fgnu89-inline",
        "-fbracket-depth=100000",
        "-emit-llvm",
        "-c",
        "-g",
    ]
    if addargs:
        cmd += addargs
    cmd += ["-o", outp, path]
    _run(cmd)
    dbg("Compiled to {0}".format(outp))

    return outp


def link_llvm(paths, outp=None, outd="/tmp/"):
    dbg("Linking {0}".format(paths))

    if outp is None:
        outp = pathjoin(outd, "code.bc")

    cmd = ["llvm-link", "-o", outp] + paths
    _run(cmd)

    dbg("Linked files to {0}".format(outp))

    return outp


def compile_and_link(files, outd, addargs=None):
    c_files, llvm_files = sort_input_files(files)
    if c_files:
        for f in c_files:
            llvm_files.append(compile_c(f, addargs=addargs))

    assert len(llvm_files) > 0, "No input files"
    if len(llvm_files) > 1:
        bitcode = link_llvm(llvm_files, outd=outd)
    else:
        bitcode = llvm_files[0]

    return bitcode
