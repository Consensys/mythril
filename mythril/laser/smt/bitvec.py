"""This module provides classes for an SMT abstraction of bit vectors."""

from typing import Union, overload, List, cast, Any, Optional

import z3

from mythril.laser.smt.bool import Bool, And
from mythril.laser.smt.expression import Expression

Annotations = List[Any]

# fmt: off


class BitVec(Expression[z3.BitVecRef]):
    """A bit vector symbol."""

    def __init__(self, raw: z3.BitVecRef, annotations: Optional[Annotations] = None):
        """

        :param raw:
        :param annotations:
        """
        super().__init__(raw, annotations)

    def size(self) -> int:
        """TODO: documentation

        :return:
        """
        return self.raw.size()

    @property
    def symbolic(self) -> bool:
        """Returns whether this symbol doesn't have a concrete value.

        :return:
        """
        self.simplify()
        return not isinstance(self.raw, z3.BitVecNumRef)

    @property
    def value(self) -> Optional[int]:
        """Returns the value of this symbol if concrete, otherwise None.

        :return:
        """
        if self.symbolic:
            return None
        assert isinstance(self.raw, z3.BitVecNumRef)
        return self.raw.as_long()

    def __add__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """Create an addition expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other + self
        if isinstance(other, int):
            return BitVec(self.raw + other, annotations=self.annotations)

        union = self.annotations + other.annotations
        return BitVec(self.raw + other.raw, annotations=union)

    def __sub__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """Create a subtraction expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other - self
        if isinstance(other, int):
            return BitVec(self.raw - other, annotations=self.annotations)

        union = self.annotations + other.annotations
        return BitVec(self.raw - other.raw, annotations=union)

    def __mul__(self, other: "BitVec") -> "BitVec":
        """Create a multiplication expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other * self
        union = self.annotations + other.annotations
        return BitVec(self.raw * other.raw, annotations=union)

    def __truediv__(self, other: "BitVec") -> "BitVec":
        """Create a signed division expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other / self
        union = self.annotations + other.annotations
        return BitVec(self.raw / other.raw, annotations=union)

    def __and__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """Create an and expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other & self
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations + other.annotations
        return BitVec(self.raw & other.raw, annotations=union)

    def __or__(self, other: "BitVec") -> "BitVec":
        """Create an or expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other | self
        union = self.annotations + other.annotations
        return BitVec(self.raw | other.raw, annotations=union)

    def __xor__(self, other: "BitVec") -> "BitVec":
        """Create a xor expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other ^ self
        union = self.annotations + other.annotations
        return BitVec(self.raw ^ other.raw, annotations=union)

    def __lt__(self, other: "BitVec") -> Bool:
        """Create a signed less than expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other > self
        union = self.annotations + other.annotations
        return Bool(self.raw < other.raw, annotations=union)

    def __gt__(self, other: "BitVec") -> Bool:
        """Create a signed greater than expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other < self
        union = self.annotations + other.annotations
        return Bool(self.raw > other.raw, annotations=union)

    def __le__(self, other: "BitVec") -> Bool:
        """Create a signed less than expression.

        :param other:
        :return:
        """
        union = self.annotations + other.annotations
        return Bool(self.raw <= other.raw, annotations=union)

    def __ge__(self, other: "BitVec") -> Bool:
        """Create a signed greater than expression.

        :param other:
        :return:
        """
        union = self.annotations + other.annotations
        return Bool(self.raw >= other.raw, annotations=union)

    # MYPY: fix complains about overriding __eq__
    def __eq__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an equality expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other == self
        if not isinstance(other, BitVec):
            return Bool(
                cast(z3.BoolRef, self.raw == other), annotations=self.annotations
            )

        union = self.annotations + other.annotations
        # MYPY: fix complaints due to z3 overriding __eq__
        return Bool(cast(z3.BoolRef, self.raw == other.raw), annotations=union)

    # MYPY: fix complains about overriding __ne__
    def __ne__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an inequality expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other != self
        if not isinstance(other, BitVec):
            return Bool(
                cast(z3.BoolRef, self.raw != other), annotations=self.annotations
            )

        union = self.annotations + other.annotations
        # MYPY: fix complaints due to z3 overriding __eq__
        return Bool(cast(z3.BoolRef, self.raw != other.raw), annotations=union)


def If(a: Union[Bool, bool], b: Union[BitVec, int], c: Union[BitVec, int]) -> BitVec:
    """Create an if-then-else expression.

    :param a:
    :param b:
    :param c:
    :return:
    """
    # TODO: Handle BitVecFunc

    if not isinstance(a, Bool):
        a = Bool(z3.BoolVal(a))
    if not isinstance(b, BitVec):
        b = BitVec(z3.BitVecVal(b, 256))
    if not isinstance(c, BitVec):
        c = BitVec(z3.BitVecVal(c, 256))
    union = a.annotations + b.annotations + c.annotations
    return BitVec(z3.If(a.raw, b.raw, c.raw), union)


def UGT(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned greater than expression.

    :param a:
    :param b:
    :return:
    """
    annotations = a.annotations + b.annotations
    if isinstance(a, BitVecFunc):
        if not a.symbolic and not b.symbolic:
            return Bool(z3.UGT(a.raw, b.raw), annotations=annotations)

        if (
            not isinstance(b, BitVecFunc)
            or not a.func_name
            or not a.input_
            or not a.func_name == b.func_name
        ):
            return Bool(z3.BoolVal(False), annotations=annotations)

        return And(
            Bool(z3.UGT(a.raw, b.raw), annotations=annotations), a.input_ != b.input_
        )

    return Bool(z3.UGT(a.raw, b.raw), annotations)


def UGE(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned greater or equals expression.

    :param a:
    :param b:
    :return:
    """
    annotations = a.annotations + b.annotations
    if isinstance(a, BitVecFunc):
        if not a.symbolic and not b.symbolic:
            return Bool(z3.UGE(a.raw, b.raw), annotations=annotations)

        if (
            not isinstance(b, BitVecFunc)
            or not a.func_name
            or not a.input_
            or not a.func_name == b.func_name
        ):
            return Bool(z3.BoolVal(False), annotations=annotations)

        return And(
            Bool(z3.UGE(a.raw, b.raw), annotations=annotations), a.input_ != b.input_
        )

    return Bool(z3.UGE(a.raw, b.raw), annotations)


def ULT(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned less than expression.

    :param a:
    :param b:
    :return:
    """
    annotations = a.annotations + b.annotations
    if isinstance(a, BitVecFunc):
        if not a.symbolic and not b.symbolic:
            return Bool(z3.ULT(a.raw, b.raw), annotations=annotations)

        if (
            not isinstance(b, BitVecFunc)
            or not a.func_name
            or not a.input_
            or not a.func_name == b.func_name
        ):
            return Bool(z3.BoolVal(False), annotations=annotations)

        return And(
            Bool(z3.ULT(a.raw, b.raw), annotations=annotations), a.input_ != b.input_
        )

    return Bool(z3.ULT(a.raw, b.raw), annotations)


@overload
def Concat(*args: List[BitVec]) -> BitVec:    ...


@overload
def Concat(*args: BitVec) -> BitVec:    ...


def Concat(*args: Union[BitVec, List[BitVec]]) -> BitVec:
    """Create a concatenation expression.

    :param args:
    :return:
    """
    # The following statement is used if a list is provided as an argument to concat
    if len(args) == 1 and isinstance(args[0], list):
        bvs = args[0] # type: List[BitVec]
    else:
        bvs = cast(List[BitVec], args)

    nraw = z3.Concat([a.raw for a in bvs])
    annotations = [] # type: Annotations
    bitvecfunc = False
    for bv in bvs:
        annotations += bv.annotations
        if isinstance(bv, BitVecFunc):
            bitvecfunc = True

    if bitvecfunc:
        # Is there a better value to set func_name and input to in this case?
        return BitVecFunc(raw=nraw, func_name=None, input_=None, annotations=annotations)

    return BitVec(nraw, annotations)


def Extract(high: int, low: int, bv: BitVec) -> BitVec:
    """Create an extract expression.

    :param high:
    :param low:
    :param bv:
    :return:
    """
    raw = z3.Extract(high, low, bv.raw)
    if isinstance(bv, BitVecFunc):
        # Is there a better value to set func_name and input to in this case?
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=bv.annotations)

    return BitVec(raw, annotations=bv.annotations)


def URem(a: BitVec, b: BitVec) -> BitVec:
    """Create an unsigned remainder expression.

    :param a:
    :param b:
    :return:
    """
    raw = z3.URem(a.raw, b.raw)
    union = a.annotations + b.annotations

    if isinstance(a, BitVecFunc) and isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=union)
    elif isinstance(a, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=a.func_name, input_=a.input_, annotations=union)
    elif isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=b.func_name, input_=b.input_, annotations=union)

    return BitVec(raw, annotations=union)


def SRem(a: BitVec, b: BitVec) -> BitVec:
    """Create a signed remainder expression.

    :param a:
    :param b:
    :return:
    """
    raw = z3.SRem(a.raw, b.raw)
    union = a.annotations + b.annotations

    if isinstance(a, BitVecFunc) and isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=union)
    elif isinstance(a, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=a.func_name, input_=a.input_, annotations=union)
    elif isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=b.func_name, input_=b.input_, annotations=union)

    return BitVec(raw, annotations=union)


def UDiv(a: BitVec, b: BitVec) -> BitVec:
    """Create an unsigned division expression.

    :param a:
    :param b:
    :return:
    """
    raw = z3.UDiv(a.raw, b.raw)
    union = a.annotations + b.annotations

    if isinstance(a, BitVecFunc) and isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=union)
    elif isinstance(a, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=a.func_name, input_=a.input_, annotations=union)
    elif isinstance(b, BitVecFunc):
        return BitVecFunc(raw=raw, func_name=b.func_name, input_=b.input_, annotations=union)

    return BitVec(raw, annotations=union)


def Sum(*args: BitVec) -> BitVec:
    """Create sum expression.

    :return:
    """
    raw = z3.Sum([a.raw for a in args])
    annotations = [] # type: Annotations
    bitvecfuncs = []

    for bv in args:
        annotations += bv.annotations
        if isinstance(bv, BitVecFunc):
            bitvecfuncs.append(bv)

    if len(bitvecfuncs) >= 2:
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=annotations)
    elif len(bitvecfuncs) == 1:
        return BitVecFunc(
            raw=raw,
            func_name=bitvecfuncs[0].func_name,
            input_=bitvecfuncs[0].input_,
            annotations=annotations,
        )

    return BitVec(raw, annotations)


def BVAddNoOverflow(a: Union[BitVec, int], b: Union[BitVec, int], signed: bool) -> Bool:
    """Creates predicate that verifies that the addition doesn't overflow.

    :param a:
    :param b:
    :param signed:
    :return:
    """
    if not isinstance(a, BitVec):
        a = BitVec(z3.BitVecVal(a, 256))
    if not isinstance(b, BitVec):
        b = BitVec(z3.BitVecVal(b, 256))
    return Bool(z3.BVAddNoOverflow(a.raw, b.raw, signed))


def BVMulNoOverflow(a: Union[BitVec, int], b: Union[BitVec, int], signed: bool) -> Bool:
    """Creates predicate that verifies that the multiplication doesn't
    overflow.

    :param a:
    :param b:
    :param signed:
    :return:
    """
    if not isinstance(a, BitVec):
        a = BitVec(z3.BitVecVal(a, 256))
    if not isinstance(b, BitVec):
        b = BitVec(z3.BitVecVal(b, 256))
    return Bool(z3.BVMulNoOverflow(a.raw, b.raw, signed))


def BVSubNoUnderflow(
    a: Union[BitVec, int], b: Union[BitVec, int], signed: bool
) -> Bool:
    """Creates predicate that verifies that the subtraction doesn't overflow.

    :param a:
    :param b:
    :param signed:
    :return:
    """
    if not isinstance(a, BitVec):
        a = BitVec(z3.BitVecVal(a, 256))
    if not isinstance(b, BitVec):
        b = BitVec(z3.BitVecVal(b, 256))

    return Bool(z3.BVSubNoUnderflow(a.raw, b.raw, signed))


# TODO: Fix circular import issues
from mythril.laser.smt.bitvecfunc import BitVecFunc
