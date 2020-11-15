from slowbeast.util.debugging import warn
from slowbeast.domains.constants import ConstantTrue, ConstantFalse
from slowbeast.domains.concrete import ConcreteVal
from slowbeast.ir.types import IntType, FloatType


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

def _get_float(s):
    try:
        if s.startswith("0x"):
            return int(s, 16)
        else:
            return float(s)
    except ValueError:
        return None


def _bitwidth(ty):
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


def is_pointer_ty(ty):
    if isinstance(ty, str):
        return ty[-1] == "*"

    assert ty.is_pointer == is_pointer_ty(str(ty))
    return ty.is_pointer


def is_array_ty(ty):
    if isinstance(ty, str):
        if len(ty) < 2:
            return False
        return ty[0] == "[" and ty[-1] == "]"
    assert ty.is_array == is_array_ty(str(ty))
    return ty.is_array


def parseArrayTyByParts(ty):
    print(parts)


def getArrayTySize(m, ty):
    assert is_array_ty(ty)
    sty = str(ty)
    parts = sty.split()
    assert parts[1] == "x", "Invalid array type"
    assert parts[0].startswith("[")
    assert parts[-1].endswith("]")
    return int(parts[0][1:]) * type_size_in_bits(m, " ".join(parts[2:])[:-1])


def type_size_in_bits(m, ty):
    if not isinstance(ty, str) and hasattr(m, 'get_type_size'):
        return m.get_type_size(ty)

    # FIXME: get rid of parsing str
    # FIXME: get rid of the magic constants and use the layout from the program
    POINTER_SIZE=64
    if not isinstance(ty, str):
        if ty.is_pointer:
            return POINTER_SIZE
        if ty.is_struct:
            return None # unsupported

    sty = str(ty)
    if is_array_ty(ty):
        return getArrayTySize(m, ty)
    elif is_pointer_ty(ty):
        return POINTER_SIZE
    elif sty == "double":
        return 64
    elif sty == "float":
        return 32
    else:
        assert "*" not in sty, "Unsupported type: {0}".format(sty)
        return _bitwidth(sty)
    return None


def type_size(m, ty):
    ts = type_size_in_bits(m, ty)
    if ts is not None:
        if ts == 0:
            return 0
        return int(max(ts / 8, 1))
    return None


def getConstant(val):
    # good, this is so ugly. But llvmlite does
    # not provide any other way...
    if val.type.is_pointer:
        return None

    if "*" in str(val):
        return None
    parts = str(val).split()
    if len(parts) != 2:
        return None

    isfloat = parts[0] in ("float", "double")
    bw = _bitwidth(parts[0])
    if not bw:
        return None

    if isfloat:
        c = _get_float(parts[1])
    else:
        c = _getInt(parts[1])
    if c is None:
        if bw == 1:
            if parts[1] == "true":
                return ConstantTrue
            elif parts[1] == "false":
                return ConstantFalse
        return None

    return ConcreteVal(c, FloatType(bw) if isfloat else IntType(bw))


def getConstantPtr(val):
    # good, this is so ugly. But llvmlite does
    # not provide any other way...
    if not val.type.is_pointer:
        return None

    # FIXME
    return None

def get_constant(val):
    if val.type.is_pointer:
        return getConstantPtr(val)


def getLLVMOperands(inst):
    return [x for x in inst.operands]
