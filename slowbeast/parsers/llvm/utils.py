from slowbeast.util.debugging import warn
from slowbeast.ir.value import Constant, ConstantTrue, ConstantFalse, Pointer
from slowbeast.ir.types import Type


def _getInt(s):
    try:
        if s.startswith("0x"):
            return int(s, 16)
        else:
            if "e" in s:  # scientific notation
                if float(s) > 0 or float(s) < 0:
                    warn("Concretized float number: {0}".format(s))
                    # return None
                return int(float(s))
            else:
                return int(s)
    except ValueError:
        return None


def _getBitWidth(ty):
    if len(ty) < 2:
        return None
    if ty[0] == "i":
        return _getInt(ty[1:])
    elif ty.startswith("double"):
        # FIXME: get this from program
        return 64
    elif ty.startswith("float"):
        return 32
    else:
        return None


def is_pointerTy(ty):
    if isinstance(ty, str):
        return ty[-1] == "*"

    assert ty.is_pointer == is_pointerTy(str(ty))
    return ty.is_pointer


def isArrayTy(ty):
    sty = str(ty)
    if len(sty) < 2:
        return False
    return sty[0] == "[" and sty[-1] == "]"


def parseArrayTyByParts(ty):
    print(parts)


def getArrayTySize(ty):
    assert isArrayTy(ty)
    sty = str(ty)
    parts = sty.split()
    assert parts[1] == "x", "Invalid array type"
    assert parts[0].startswith("[")
    assert parts[-1].endswith("]")
    return int(parts[0][1:]) * getTypeSizeInBits(" ".join(parts[2:])[:-1])


def getTypeSizeInBits(ty):
    # FIXME: get rid of the magic constants and use the layout from the program
    if not isinstance(ty, str) and ty.is_pointer:
        return 64

    sty = str(ty)
    if isArrayTy(ty):
        s = getArrayTySize(ty)
        return s
    elif is_pointerTy(ty):
        return 64
    elif sty == "double":
        return 64
    elif sty == "float":
        return 32
    else:
        assert "*" not in sty, "Unsupported type: {0}".format(sty)
        return _getBitWidth(sty)


def getTypeSize(ty):
    ts = getTypeSizeInBits(ty)
    if ts is not None:
        if ts == 0:
            return 0
        return int(max(ts / 8, 1))
    return None


def getConstantInt(val):
    # good, this is so ugly. But llvmlite does
    # not provide any other way...
    if val.type.is_pointer:
        return None

    if "*" in str(val):
        return None
    parts = str(val).split()
    if len(parts) != 2:
        return None

    bw = _getBitWidth(parts[0])
    if not bw:
        return None

    c = _getInt(parts[1])
    if c is None:
        if bw == 1:
            if parts[1] == "true":
                return ConstantTrue
            elif parts[1] == "false":
                return ConstantFalse
        return None

    return Constant(c, Type(bw))


def getConstantPtr(val):
    # good, this is so ugly. But llvmlite does
    # not provide any other way...
    if not val.type.is_pointer:
        return None

    if str(val).endswith("null"):
        return Pointer(0)
    return None


def getLLVMOperands(inst):
    return [x for x in inst.operands]
