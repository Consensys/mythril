from typing import Union, overload, List, Set, cast, Any, Optional, Callable
from operator import lshift, rshift, ne, eq
import z3

from mythril.laser.smt.bool import Bool, And, Or
from mythril.laser.smt.bitvec import BitVec
from mythril.laser.smt.bitvecfunc import BitVecFunc
from mythril.laser.smt.bitvecfunc import _arithmetic_helper as _func_arithmetic_helper
from mythril.laser.smt.bitvecfunc import _comparison_helper as _func_comparison_helper

Annotations = Set[Any]


def _comparison_helper(
    a: BitVec, b: BitVec, operation: Callable, default_value: bool, inputs_equal: bool
) -> Bool:
    annotations = a.annotations.union(b.annotations)
    if isinstance(a, BitVecFunc):
        return _func_comparison_helper(a, b, operation, default_value, inputs_equal)
    return Bool(operation(a.raw, b.raw), annotations)


def _arithmetic_helper(a: BitVec, b: BitVec, operation: Callable) -> BitVec:
    raw = operation(a.raw, b.raw)
    union = a.annotations.union(b.annotations)

    if isinstance(a, BitVecFunc):
        return _func_arithmetic_helper(a, b, operation)
    elif isinstance(b, BitVecFunc):
        return _func_arithmetic_helper(b, a, operation)

    return BitVec(raw, annotations=union)


def LShR(a: BitVec, b: BitVec):
    return _arithmetic_helper(a, b, z3.LShR)


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
    union = a.annotations.union(b.annotations).union(c.annotations)

    bvf = []  # type: List[BitVecFunc]
    if isinstance(a, BitVecFunc):
        bvf += [a]
    if isinstance(b, BitVecFunc):
        bvf += [b]
    if isinstance(c, BitVecFunc):
        bvf += [c]
    if bvf:
        raw = z3.If(a.raw, b.raw, c.raw)
        nested_functions = [nf for func in bvf for nf in func.nested_functions] + bvf
        return BitVecFunc(raw, func_name="Hybrid", nested_functions=nested_functions)

    return BitVec(z3.If(a.raw, b.raw, c.raw), union)


def UGT(a: BitVec, b: BitVec) -> Bool:
    """Create an unsigned greater than expression.

    :param a:
    :param b:
    :return:
    """
    return _comparison_helper(a, b, z3.UGT, default_value=False, inputs_equal=False)


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
    return _comparison_helper(a, b, z3.ULT, default_value=False, inputs_equal=False)


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

    nested_functions = []  # type: List[BitVecFunc]
    for bv in bvs:
        annotations = annotations.union(bv.annotations)
        if isinstance(bv, BitVecFunc):
            nested_functions += bv.nested_functions
            nested_functions += [bv]

    if nested_functions:
        return BitVecFunc(
            raw=nraw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec("", 256), annotations=annotations),
            nested_functions=nested_functions,
        )

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
        input_string = ""
        # Is there a better value to set func_name and input to in this case?
        return BitVecFunc(
            raw=raw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec(input_string, 256), annotations=bv.annotations),
            nested_functions=bv.nested_functions + [bv],
        )

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
    bitvecfuncs = []

    for bv in args:
        annotations = annotations.union(bv.annotations)
        if isinstance(bv, BitVecFunc):
            bitvecfuncs.append(bv)

    nested_functions = [
        nf for func in bitvecfuncs for nf in func.nested_functions
    ] + bitvecfuncs

    if len(bitvecfuncs) >= 2:
        return BitVecFunc(
            raw=raw,
            func_name="Hybrid",
            input_=None,
            annotations=annotations,
            nested_functions=nested_functions,
        )
    elif len(bitvecfuncs) == 1:
        return BitVecFunc(
            raw=raw,
            func_name=bitvecfuncs[0].func_name,
            input_=bitvecfuncs[0].input_,
            annotations=annotations,
            nested_functions=nested_functions,
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
