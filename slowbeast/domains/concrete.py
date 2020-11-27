from slowbeast.ir.types import IntType, BoolType, Type, PointerType
from slowbeast.domains.value import Value
from slowbeast.ir.instruction import FpOp
from slowbeast.util.debugging import FIXME
from math import isinf, isnan, isfinite

from struct import pack, unpack


def trunc_to_float(x, ty):
    # isnt there a more efficient way? Probably just to use numpy.float32
    # (but it seem to use a different rounding mode), or write the float
    # handling directly in C (there must be a library with Python bindings
    # for that)
    if ty.bitwidth() == 32:
        return unpack("f", pack("f", x))[0]
    return x

def float_to_bv(x, unsigned=True):
    if not x.is_float():
        return x.value()
    bw = x.bitwidth()
    if bw == 32:
        d = (unpack("I", pack("f", x.value())) if unsigned else unpack("i", pack("f", x.value())))[0]
    else:
        assert bw == 64, f"{x}, bw: {bw}"
        d = (unpack("L", pack("d", x.value())) if unsigned else unpack("l", pack("d", x.value())))[0]
    return d

def to_unsigned(x, bw):
    """ Get unsigned value for signed in 2's complement """
    if x >= 0:
        return x
    return x + (1 << bw)


def wrap_to_bw(x, bw):
    m = 1 << bw
    if x >= 0:
        while x >= m:
            x -= m
    else:
        m = m
        while x <= -m:
            x += m
    return x


def dom_is_concrete(v):
    return v.KIND == 1


class ConcreteVal(Value):
    """
    Integer constant or boolean
    """

    KIND = 1

    __slots__ = ["_value"]

    def __init__(self, c, ty):
        assert isinstance(c, (int, bool, float)), f"Invalid constant: {c} {type(c)}"
        assert isinstance(ty, Type), f"Invalid type: {ty}"
        assert not isinstance(ty, PointerType), f"Invalid type: {ty}"
        super().__init__(ty)
        self._value = c

        assert not self.is_pointer(), "Incorrectly constructed pointer"
        assert not self.is_bool() or (c in (True, False)), "Invalid boolean constant"
        assert self.is_bool() or isinstance(c, (int, float))

    def as_value(self):
        return "{0}:{1}".format(str(self._value), self.type())

    def value(self):
        return self._value

    def is_concrete(self):
        return True

    def __repr__(self):
        return f"{self._value}:{self.type()}"

    def __hash__(self):
        return self._value

    def __eq__(self, rhs):
        assert isinstance(rhs, ConcreteVal)
        return self.value() == rhs.value() and self.type() == rhs.type()


class ConcreteBool(ConcreteVal):
    def __init__(self, b):
        assert isinstance(b, bool), b
        super().__init__(b, BoolType())


class ConcreteInt(ConcreteVal):
    def __init__(self, n, bw):
        assert isinstance(n, int), n
        assert isinstance(bw, int), bw
        super().__init__(n, IntType(bw))


class ConcreteDomain:
    """
    Takes care of handling concrete computations.
    """

    def belongto(*args):
        assert len(args) > 0
        for a in args:
            assert isinstance(a, Value), a
            if a.KIND != 1:
                return False
        return True

    def Value(c, bw):
        if isinstance(c, bool):
            assert bw == 1
            return ConcreteBool(c)
        return ConcreteInt(c, bw)

    def getTrue():
        return ConcreteBool(True)

    def getFalse():
        return ConcreteBool(False)

    def conjunction(*args):
        """
        And() of multiple boolean arguments.
        And() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical and,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteBool(all(map(lambda x: x.value() is True, args)))

    def disjunction(*args):
        """
        Or() of multiple boolean arguments.
        Or() itself works as logical or bitwise and depending
        on the arguments.  This method is only logical or,
        but of multiple arguments"""
        assert ConcreteDomain.belongto(*args)
        assert all(map(lambda a: a.is_bool(), args))
        return ConcreteBool(any(map(lambda x: x.value() is True, args)))

    def Ite(c, a, b):
        assert dom_is_concrete(c)
        assert c.is_bool(), c
        assert a.type() == b.type(), f"{a}, {b}"
        return a if c else b

    def And(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBool(a.value() and b.value())
        else:
            return ConcreteVal(float_to_bv(a) & float_to_bv(b),
                               IntType(a.bitwidth()))

    def Or(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        if a.is_bool():
            return ConcreteBool(a.value() or b.value())
        else:
            return ConcreteVal(float_to_bv(a) | float_to_bv(b),
                               IntType(a.bitwidth()))

    def Xor(a, b):
        assert a.bitwidth() == b.bitwidth(), f"{a}, {b}"
        assert a.type() == b.type()
        return ConcreteVal(float_to_bv(a) ^ float_to_bv(b),
                           IntType(a.bitwidth()))

    def Not(a):
        assert ConcreteDomain.belongto(a)
        if a.is_bool():
            return ConcreteBool(not a.value())
        else:
            return ConcreteVal(~float_to_bv(a), a.type())

    def ZExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.is_int() or a.is_bool(), a
        assert a.bitwidth() < b.value(), "Invalid zext argument"
        return ConcreteInt(to_unsigned(a.value(), a.bitwidth()), b.value())

    def SExt(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.is_int(), a
        assert a.bitwidth() <= b.value(), "Invalid sext argument"
        sb = 1 << (b.value() - 1)
        val = (a.value() & (sb - 1)) - (a.value() & sb)
        return ConcreteInt(val, b.value())

    def Cast(a: ConcreteVal, ty: Type):
        """
        Reinterpret cast
        """
        assert ConcreteDomain.belongto(a)
        if a.is_int():
            if ty.is_float():
                return ConcreteVal(trunc_to_float(float(a.value()), ty), ty)
            elif ty.is_int():
                return ConcreteVal(a.value(), ty)
        elif a.is_float():
            if ty.is_float():
                return ConcreteVal(trunc_to_float(a.value(), ty), ty)
            elif ty.is_int():
               return ConcreteVal(float_to_bv(a), ty)
        return None  # unsupported conversion

    def Shl(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ConcreteVal(a.value() << b.value(), a.type())

    def AShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        return ConcreteVal(a.value() >> b.value(), a.type())

    def LShr(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() < a.bitwidth(), "Invalid shift"
        val = a.value()
        return ConcreteVal(
            a.value() >> b.value()
            if val >= 0
            else (val + (1 << a.bitwidth())) >> b.value(),
            a.type(),
        )

    def Extract(a, start, end):
        assert ConcreteDomain.belongto(a)
        assert start.is_concrete()
        assert end.is_concrete()
        bitsnum = end.value() - start.value() + 1
        return ConcreteInt(
            (a.value() >> start.value()) & ((1 << (bitsnum)) - 1), bitsnum
        )

    def Concat(a, b):
        assert ConcreteDomain.belongto(a, b)
        bw = b.bitwidth()
        return ConcreteInt(
            ((a.value() << bw) | b.value()), a.bitwidth() + bw,
        )


    def Rem(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        assert b.value() != 0, "Invalid remainder"
        if unsigned:
            return ConcreteVal(to_unsigned(a.value(), a.bitwidth()) %
                               to_unsigned(b.value(), b.bitwidth()), a.type())
        return ConcreteVal(a.value() % b.value(), a.type())

    def Neg(a):
        """ Return the negated number """
        assert ConcreteDomain.belongto(a, b)
        ty = a.type()
        if a.is_float():
            return ConcreteVal(trunc_to_float(-a.value(), ty), ty)
        return ConcreteVal(wrap_to_bw(-a.value(), ty.bitwidth()), ty)

    def Abs(a):
        assert ConcreteDomain.belongto(a)
        return ConcreteVal(abs(a.value()), a.type())

    def FpOp(op, val):
        assert ConcreteDomain.belongto(val)
        # FIXME: do not use the enum from instruction
        assert val.is_float(), val

        if op == FpOp.IS_INF:
            return ConcreteBool(isinf(val.value()))
        if op == FpOp.IS_NAN:
            return ConcreteBool(isnan(val.value()))
        if op == FpOp.FPCLASSIFY:
            FIXME("Using implementation dependent constants")
            v = val.value()
            if isnan(v): return ConcreteInt(0, 32)
            if isinf(v): return ConcreteInt(1, 32)
            if v >= 0 and v <= 0: return ConcreteInt(2, 32)
            if isfinite(v): return ConcreteInt(4, 32)
            return ConcreteInt(3, 32) # subnormal
        if op == FpOp.SIGNBIT:
            # FIXME! gosh this is ugly...
            return ConcreteInt(1 if str(val.value())[0] == '-' else 0, 32)
        raise NotImplementedError("Invalid/unsupported FP operation")

    ##
    # Relational operators
    def Le(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval <= bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval <= bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) <= to_unsigned(bval, bw))
        return ConcreteBool(aval <= bval)

    def Lt(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval < bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval < bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) < to_unsigned(bval, bw))
        return ConcreteBool(aval < bval)

    def Ge(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval >= bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval >= bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) >= to_unsigned(bval, bw))
        return ConcreteBool(aval >= bval)

    def Gt(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval > bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval > bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) > to_unsigned(bval, bw))
        return ConcreteBool(aval > bval)


    def Eq(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval == bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval == bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) == to_unsigned(bval, bw))
        return ConcreteBool(aval == bval)

    def Ne(a, b, unsigned=False, floats=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.bitwidth() == b.bitwidth(), f"{a.type()} != {b.type()}"
        if floats:
            aval, bval = float(a.value()), float(b.value())
            if unsigned: # means unordered for floats
                return ConcreteBool(aval != bval)
            return ConcreteBool(not isnan(aval) and not isnan(bval) and aval != bval)

        aval, bval = float_to_bv(a, unsigned), float_to_bv(b, unsigned)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteBool(to_unsigned(aval, bw) != to_unsigned(bval, bw))
        return ConcreteBool(aval != bval)



    ##
    # Arithmetic operations
    def Add(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float()
        # FIXME: add self-standing float domain?
        ty = a.type()
        if a.is_float():
            return ConcreteVal(trunc_to_float(a.value() + b.value(), ty), ty)
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() + b.value(), bw), ty)

    def Sub(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float()
        ty = a.type()
        if a.is_float():
            return ConcreteVal(trunc_to_float(a.value() - b.value(), ty), ty)
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() - b.value(), bw), ty)

    def Mul(a, b):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a.type()} != {b.type()}"
        assert a.is_int() or a.is_float()
        ty = a.type()
        if a.is_float():
            return ConcreteVal(trunc_to_float(a.value() * b.value(), ty), ty)
        bw = a.type().bitwidth()
        return ConcreteVal(wrap_to_bw(a.value() * b.value(), bw), ty)

    def Div(a, b, unsigned=False):
        assert ConcreteDomain.belongto(a, b)
        assert a.type() == b.type(), f"{a}, {b}"
        assert a.is_int() or a.is_float()
        result_ty = a.type()
        if a.is_float():
            if b.value() == 0:
                aval = a.value()
                if aval > 0:
                    return ConcreteVal(trunc_to_float(float("inf"), result_ty), result_ty)
                if aval < 0:
                    return ConcreteVal(trunc_to_float(float("-inf"),
                                                      result_ty), result_ty)
                else:
                    return ConcreteVal(trunc_to_float(float("NaN"), result_ty),
                                       result_ty)
            return ConcreteVal(trunc_to_float(a.value() / b.value(), result_ty),
                               result_ty)
        if unsigned:
            bw = a.bitwidth()
            return ConcreteVal(to_unsigned(a.value(), bw) /
                               to_unsigned(b.value(), bw), result_ty)
        return ConcreteVal(
            wrap_to_bw(int(a.value() / b.value()), result_ty.bitwidth()), result_ty
        )
