from typing import Union, overload, List, Set, cast, Any, Callable
import z3
from copy import copy
from mythril.laser.smt.bool import Bool, Or
from mythril.laser.smt.bitvec import BitVec, BitVecExtract
from mythril.laser.smt.bitvecfunc import BitVecFunc
from mythril.laser.smt.bitvecfunc import BitVecFuncExtract
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


def check_extracted_var(bv: BitVec) -> bool:
    return isinstance(bv, BitVecFuncExtract) or isinstance(bv, BitVecExtract)


def concat_helper(bvs: List[BitVec]) -> List[BitVec]:
    """
    Automatically concatenat the adjacent symbols which are
    concatenate-able(like Concatenating Extract(10, 8, a) and Extract(7, 0, a) to Extract(10, 0, a))
    :param bvs: List of Bitvecs
    :return: List of Bitvecs with some concats
    """
    prev_bv = copy(bvs[0])
    new_bvs = []
    # casting everywhere in "if's" will look quite messy, so I am type ignoring them.
    for bv in bvs[1:]:
        if (
            not (check_extracted_var(bv) and check_extracted_var(prev_bv))
            or bv.high + 1 != prev_bv.low  # type: ignore
            or z3.simplify(bv.parent.raw != prev_bv.parent.raw)  # type: ignore
        ):

            if check_extracted_var(prev_bv) and hash(prev_bv) == hash(
                prev_bv.parent  # type: ignore
            ):
                new_bvs.append(prev_bv.parent)  # type: ignore
            else:
                new_bvs.append(prev_bv)
            prev_bv = copy(bv)
            continue
        prev_bv.raw = z3.simplify(z3.Concat(prev_bv.raw, bv.raw))
        prev_bv.low = bv.low  # type: ignore
    if check_extracted_var(prev_bv) and hash(z3.simplify(prev_bv.raw)) == hash(
        prev_bv.parent  # type: ignore
    ):
        prev_bv = prev_bv.parent  # type: ignore
    new_bvs.append(prev_bv)
    if (
        len(new_bvs) == 1
        and check_extracted_var(new_bvs[0])
        and hash(z3.simplify(new_bvs[0].raw))
        == hash(z3.simplify(new_bvs[0].parent.raw))
    ):
        return new_bvs[0].parent
    return new_bvs


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
    new_bvs = concat_helper(bvs)
    if len(new_bvs) == 1:
        return new_bvs[0]
    if nested_functions:
        return BitVecFunc(
            raw=nraw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec("", 256), annotations=annotations),
            nested_functions=nested_functions,
            concat_args=new_bvs,
        )

    return BitVec(raw=nraw, annotations=annotations, concat_args=new_bvs)


def extract_helper(high: int, low: int, bv: BitVec) -> BitVec:
    """
    Extracts from the list of bitvecs which were supposedly concatenated.
    :param high:
    :param low:
    :param bv:
    :return:
    """
    count = 0
    val = None
    for small_bv in bv.concat_args[::-1]:
        if low == count:
            if small_bv.size() <= high - low + 1:
                val = small_bv
            else:
                val = Extract(
                    small_bv.size() - 1, small_bv.size() - (high - low + 1), small_bv
                )
        elif high < count:
            break
        elif low < count:
            if low + small_bv.size() <= high:
                val = Concat(small_bv, val)
            else:
                val = Concat(
                    Extract(
                        small_bv.size() - 1,
                        small_bv.size() - (high - low + 1),
                        small_bv,
                    ),
                    val,
                )
        count += small_bv.size()
    return val


def Extract(high: int, low: int, bv: BitVec) -> BitVec:
    """Create an extract expression.

    :param high:
    :param low:
    :param bv:
    :return:
    """
    raw = z3.Extract(high, low, bv.raw)
    val = extract_helper(high, low, bv)
    dc = copy(bv)
    if val is not None:
        val.simplify()
        bv.simplify()
        if check_extracted_var(val) and hash(val.raw) == hash(
            val.parent.raw  # type: ignore
        ):
            val = val.parent  # type: ignore
        assert val.size() == high - low + 1
        return val
    input_string = ""
    bv.simplify()
    assert raw.size() == high - low + 1
    if isinstance(bv, BitVecFunc):
        return BitVecFuncExtract(
            raw=raw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec(input_string, 256), annotations=bv.annotations),
            nested_functions=bv.nested_functions + [bv],
            low=low,
            high=high,
            parent=bv,
        )
    else:
        return BitVecExtract(raw=raw, low=low, high=high, parent=bv)


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
