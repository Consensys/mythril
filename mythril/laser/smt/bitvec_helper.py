from typing import Union, overload, List, Set, cast, Any, Callable
import z3

from mythril.laser.smt.bool import Bool, Or
from mythril.laser.smt.bitvec import BitVec
from mythril.laser.smt.array import BaseArray, Array

Annotations = Set[Any]


def _z3_array_converter(array: Union[z3.Array, z3.K]) -> Array:
    new_array = Array(
        "name_to_be_overwritten", array.domain().size(), array.range().size()
    )
    new_array.raw = array
    return new_array


def _comparison_helper(a: BitVec, b: BitVec, operation: Callable) -> Bool:
    annotations = a.annotations.union(b.annotations)
    return Bool(operation(a.raw, b.raw), annotations)


def _arithmetic_helper(a: BitVec, b: BitVec, operation: Callable) -> BitVec:
    raw = operation(a.raw, b.raw)
    union = a.annotations.union(b.annotations)
    return BitVec(raw, annotations=union)


def LShR(a: BitVec, b: BitVec):
    return _arithmetic_helper(a, b, z3.LShR)


@overload
def If(a: Union[Bool, bool], b: Union[BitVec, int], c: Union[BitVec, int]) -> BitVec:
    ...


@overload
def If(a: Union[Bool, bool], b: BaseArray, c: BaseArray) -> BaseArray:
    ...


def If(
    a: Union[Bool, bool],
    b: Union[BaseArray, BitVec, int],
    c: Union[BaseArray, BitVec, int],
) -> Union[BitVec, BaseArray]:
    """Create an if-then-else expression.

    :param a:
    :param b:
    :param c:
    :return:
    """
    if not isinstance(a, Bool):
        a = Bool(z3.BoolVal(a))

    if isinstance(b, BaseArray) and isinstance(c, BaseArray):
        array = z3.If(a.raw, b.raw, c.raw)
        return _z3_array_converter(array)

    if not isinstance(b, BitVec):
        b = BitVec(z3.BitVecVal(b, 256))
    if not isinstance(c, BitVec):
        c = BitVec(z3.BitVecVal(c, 256))
    union = a.annotations.union(b.annotations).union(c.annotations)
    return BitVec(z3.If(a.raw, b.raw, c.raw), union)


def UGT(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned greater than expression.

    :param a:
    :param b:
    :return:
    """
    return _comparison_helper(a, b, z3.UGT)


def UGE(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned greater or equals expression.

    :param a:
    :param b:
    :return:
    """
    return Or(UGT(a, b), a == b)


def ULT(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned less than expression.

    :param a:
    :param b:
    :return:
    """
    return _comparison_helper(a, b, z3.ULT)


def ULE(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned less than expression.

    :param a:
    :param b:
    :return:
    """
    return Or(ULT(a, b), a == b)


@overload
def Concat(*args: List[BitVec]) -> BitVec:
    ...


@overload
def Concat(*args: BitVec) -> BitVec:
    ...


def Concat(*args: Union[BitVec, List[BitVec]]) -> BitVec:
    """Create a concatenation expression.

    :param args:
    :return:
    """
    # The following statement is used if a list is provided as an argument to concat
    if len(args) == 1 and isinstance(args[0], list):
        bvs = args[0]  # type: List[BitVec]
    else:
        bvs = cast(List[BitVec], args)

    nraw = z3.Concat([a.raw for a in bvs])
    annotations = set()  # type: Annotations

    for bv in bvs:
        annotations = annotations.union(bv.annotations)
    return BitVec(nraw, annotations)


def Extract(high: int, low: int, bv: BitVec) -> BitVec:
    """Create an extract expression.

    :param high:
    :param low:
    :param bv:
    :return:
    """
    raw = z3.Extract(high, low, bv.raw)
    return BitVec(raw, annotations=bv.annotations)


def URem(a: BitVec, b: BitVec) -> BitVec:
    """Create an unsigned remainder expression.

    :param a:
    :param b:
    :return:
    """
    return _arithmetic_helper(a, b, z3.URem)


def SRem(a: BitVec, b: BitVec) -> BitVec:
    """Create a signed remainder expression.

    :param a:
    :param b:
    :return:
    """
    return _arithmetic_helper(a, b, z3.SRem)


def UDiv(a: BitVec, b: BitVec) -> BitVec:
    """Create an unsigned division expression.

    :param a:
    :param b:
    :return:
    """
    return _arithmetic_helper(a, b, z3.UDiv)


def Sum(*args: BitVec) -> BitVec:
    """Create sum expression.

    :return:
    """
    raw = z3.Sum([a.raw for a in args])
    annotations = set()  # type: Annotations

    for bv in args:
        annotations = annotations.union(bv.annotations)
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
