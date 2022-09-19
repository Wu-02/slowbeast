from struct import unpack, pack

from slowbeast.domains.concrete_int_float import ConstantTrue, ConstantFalse
from slowbeast.domains.concrete_value import ConcreteVal
from slowbeast.domains.pointer import Pointer, get_null_pointer
from slowbeast.ir.types import BitVecType, FloatType, PointerType
from slowbeast.util.debugging import warn
from slowbeast.domains.concrete_bool import ConcreteBool
from slowbeast.domains.concrete_int_float import ConstantTrue, ConstantFalse, ConcreteDomain
from typing import Optional, Sized, Union

concrete_value = ConcreteDomain.Value

def _getInt(s) -> Optional[int]:
    try:
        if s.startswith("0x"):
            return int(s, 16)
        else:
            if "e" in s:  # scientific notation
                if float(s) > 0 or float(s) < 0:
                    warn(f"Concretized float number: {s}")
                    # return None
                return int(float(s))
            else:
                return int(s)
    except ValueError:
        return None


def trunc_to_float(x):
    return unpack("f", pack("f", x))[0]


def to_float_ty(val: ConcreteVal) -> ConcreteVal:
    if isinstance(val, ConcreteVal):
        return concrete_value(float(val.value()), val.bitwidth())
    return val


def _get_float(s):
    try:
        if s.startswith("0x"):
            # llvm writes the constants as double
            # FIXME: get the byte order from module
            return trunc_to_float(unpack(">d", int(s, 16).to_bytes(8, "big"))[0])
        else:
            return float(s)
    except ValueError:
        return None


def _get_double(s):
    try:
        if s.startswith("0x"):
            # llvm writes the constants as double (even when it is 32 bit)
            return unpack(">d", int(s, 16).to_bytes(8, "big"))[0]
        else:
            return float(s)
    except ValueError:
        return None


def _bitwidth(ty: Sized) -> Optional[int]:
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


def is_pointer_ty(ty: str) -> bool:
    if isinstance(ty, str):
        return ty[-1] == "*"

    assert ty.is_pointer == is_pointer_ty(str(ty))
    return ty.is_pointer


def is_array_ty(ty: str) -> bool:
    if isinstance(ty, str):
        if len(ty) < 2:
            return False
        return ty[0] == "[" and ty[-1] == "]"
    assert ty.is_array == is_array_ty(str(ty))
    return ty.is_array


def parse_array_ty_by_parts(ty) -> None:
    print(parts)


def get_array_ty_size(m, ty: str) -> int:
    assert is_array_ty(ty)
    sty = str(ty)
    parts = sty.split()
    assert parts[1] == "x", "Invalid array type"
    assert parts[0].startswith("[")
    assert parts[-1].endswith("]")
    return int(parts[0][1:]) * type_size_in_bits(m, " ".join(parts[2:])[:-1])


def type_size_in_bits(m, ty: str):
    if not isinstance(ty, str) and hasattr(m, "get_type_size"):
        return m.get_type_size(ty)

    # FIXME: get rid of parsing str
    # FIXME: get rid of the magic constants and use the layout from the program
    POINTER_SIZE = 64
    if not isinstance(ty, str):
        if ty.is_pointer:
            return POINTER_SIZE
        if ty.is_struct:
            return None  # unsupported

    sty = str(ty)
    if is_array_ty(ty):
        return get_array_ty_size(m, ty)
    elif is_pointer_ty(ty):
        return POINTER_SIZE
    elif sty == "double":
        return 64
    elif sty == "float":
        return 32
    else:
        assert "*" not in sty, f"Unsupported type: {sty}"
        return _bitwidth(sty)
    return None


def type_size(m, ty: str) -> Optional[int]:
    ts = type_size_in_bits(m, ty)
    if ts is not None:
        if ts == 0:
            return 0
        return int(max(ts / 8, 1))
    return None


def get_sb_type(m, ty: str) -> Union[None, FloatType, BitVecType, PointerType]:
    if is_pointer_ty(ty):
        return PointerType()

    sty = str(ty)
    if sty in ("void", "metadata"):
        return None

    ts = type_size_in_bits(m, ty)
    if ts is None:
        return None

    if sty in ("float", "double"):
        return FloatType(ts)
    elif sty.startswith("i"):
        return BitVecType(ts)
    assert False, f"Unsupported type: {ty}"
    return None


def get_float_constant(sval, isdouble: bool = True):
    if isdouble:
        return _get_double(sval)
    return _get_float(sval)


def get_pointer_constant(val) -> Optional[Pointer]:
    assert is_pointer_ty(val.type)
    parts = str(val).split()
    if parts[-1] == "null":
        return get_null_pointer()
    return None


def get_constant(val):
    # My, this is so ugly... but llvmlite does
    # not provide any other way...
    if is_pointer_ty(val.type):
        return get_pointer_constant(val)

    parts = str(val).split()
    if len(parts) != 2:
        return None

    bw = _bitwidth(parts[0])
    if not bw:
        return None
    isdouble = parts[0] == "double"
    isfloating = parts[0] == "float" or isdouble

    if isfloating:
        c = get_float_constant(parts[1], isdouble)
    else:
        c = _getInt(parts[1])
    if c is None:
        if bw == 1:
            if parts[1] == "true":
                c = True
            elif parts[1] == "false":
                c = False
        return None

    return concrete_value(c, bw)


def bv_to_bool_else_id(bv: ConcreteBool) -> ConcreteBool:
    if bv.is_concrete():
        if bv.value() == 0:
            return ConstantFalse
        else:
            return ConstantTrue
    return bv


def get_llvm_operands(inst):
    return [x for x in inst.operands]
