import operator
from itertools import product
from typing import Optional, Union, cast, Callable, List
import z3

from mythril.laser.smt.bitvec import BitVec, Annotations
from mythril.laser.smt.bool import Or, Bool, And


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

    concat_list = bvs
    nraw = z3.Concat([a.raw for a in bvs])
    annotations = set()  # type: Annotations

    nested_functions = []  # type: List[BitVecFunc]
    bfne_cnt = 0
    parent = None
    for bv in bvs:
        annotations = annotations.union(bv.annotations)
        if isinstance(bv, BitVecFunc):
            nested_functions += bv.nested_functions
            nested_functions += [bv]
            if isinstance(bv, BitVecFuncExtract):
                if parent is None:
                    parent = bv.parent
                if hash(parent.raw) != hash(bv.parent.raw):
                    continue
                bfne_cnt += 1

    if bfne_cnt == len(bvs):
        # check for continuity
        fail = True
        if bvs[-1].low == 0:
            fail = False
            for index, bv in enumerate(bvs):
                if index == 0:
                    continue
                if bv.high + 1 != bvs[index - 1].low:
                    fail = True
                    break

        if fail is False:
            if bvs[0].high == bvs[0].parent.size() - 1:
                return bvs[0].parent
            else:
                return BitVecFuncExtract(
                    raw=nraw,
                    func_name=bvs[0].func_name,
                    input_=bvs[0].input_,
                    nested_functions=nested_functions,
                    concat_args=concat_list,
                    low=bvs[-1].low,
                    high=bvs[0].high,
                    parent=bvs[0].parent,
                )

    if nested_functions:
        for bv in bvs:
            bv.simplify()

        return BitVecFunc(
            raw=nraw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec("", 256), annotations=annotations),
            nested_functions=nested_functions,
            concat_args=concat_list,
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
        count = 0
        val = None
        for small_bv in bv.concat_args[::-1]:
            if low == count:
                if low + small_bv.size() <= high:
                    val = small_bv
                else:
                    val = Extract(
                        small_bv.size() - 1,
                        small_bv.size() - (high - low + 1),
                        small_bv,
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
        if val is not None:
            if isinstance(val, BitVecFuncExtract) and z3.simplify(
                val.raw == val.parent.raw
            ):
                val = val.parent
            val.simplify()
            return val
        input_string = ""
        # Is there a better value to set func_name and input to in this case?
        return BitVecFuncExtract(
            raw=raw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec(input_string, 256), annotations=bv.annotations),
            nested_functions=bv.nested_functions + [bv],
            low=low,
            high=high,
            parent=bv,
        )

    return BitVec(raw, annotations=bv.annotations)


def _arithmetic_helper(
    a: "BitVecFunc", b: Union[BitVec, int], operation: Callable
) -> "BitVecFunc":
    """
    Helper function for arithmetic operations on BitVecFuncs.

    :param a: The BitVecFunc to perform the operation on.
    :param b: A BitVec or int to perform the operation on.
    :param operation: The arithmetic operation to perform.
    :return: The resulting BitVecFunc
    """
    if isinstance(b, int):
        b = BitVec(z3.BitVecVal(b, a.size()))

    raw = operation(a.raw, b.raw)
    union = a.annotations.union(b.annotations)

    if isinstance(b, BitVecFunc):
        return BitVecFunc(
            raw=raw,
            func_name="Hybrid",
            input_=BitVec(z3.BitVec("{} op {}".format(a, b), 256), annotations=union),
            nested_functions=a.nested_functions + b.nested_functions + [a, b],
        )

    return BitVecFunc(
        raw=raw,
        func_name=a.func_name,
        input_=a.input_,
        annotations=union,
        nested_functions=a.nested_functions + [a],
    )


def _comparison_helper(
    a: "BitVecFunc",
    b: Union[BitVec, int],
    operation: Callable,
    default_value: bool,
    inputs_equal: bool,
) -> Bool:
    """
    Helper function for comparison operations with BitVecFuncs.

    :param a: The BitVecFunc to compare.
    :param b: A BitVec or int to compare to.
    :param operation: The comparison operation to perform.
    :return: The resulting Bool
    """
    # Is there some hack for gt/lt comparisons?
    if isinstance(b, int):
        b = BitVec(z3.BitVecVal(b, a.size()))
    union = a.annotations.union(b.annotations)

    if not a.symbolic and not b.symbolic:
        if operation == z3.UGT:
            operation = operator.gt
        if operation == z3.ULT:
            operation = operator.lt
        return Bool(z3.BoolVal(operation(a.value, b.value)), annotations=union)

    if (
        a.size() == 512
        and b.size() == 512
        and z3.is_true(
            z3.simplify(z3.Extract(255, 0, a.raw) == z3.Extract(255, 0, b.raw))
        )
    ):
        a = Extract(511, 256, a)
        b = Extract(511, 256, b)

    if not isinstance(b, BitVecFunc):
        if a.potential_value:
            condition = False
            for value, cond in a.potential_value:
                if value is not None:
                    condition = Or(condition, And(operation(b, value), cond))
            return And(condition, operation(a.raw, b.raw))

        if b.pseudo_input and b.pseudo_input.size() >= a.input_.size():
            if b.pseudo_input.size() > a.input_.size():
                padded_a = z3.Concat(
                    z3.BitVecVal(0, b.pseudo_input.size() - a.input_.size()),
                    a.input_.raw,
                )
            else:
                padded_a = a.input_.raw
            print(b.pseudo_input.raw)
            return And(operation(a.raw, b.raw), operation(padded_a, b.pseudo_input.raw))
    if (
        not isinstance(b, BitVecFunc)
        or not a.func_name
        or not a.input_
        or not a.func_name == b.func_name
        or str(operation) not in ("<built-in function eq>", "<built-in function ne>")
    ):
        return Bool(z3.BoolVal(default_value), annotations=union)

    condition = True
    for a_nest, b_nest in product(a.nested_functions, b.nested_functions):
        if a_nest.func_name != b_nest.func_name:
            continue
        if a_nest.func_name == "Hybrid":
            continue
        # a.input (eq/neq) b.input ==> a == b
        if inputs_equal:
            condition = z3.And(
                condition,
                z3.Or(
                    z3.Not((a_nest.input_ == b_nest.input_).raw),
                    (a_nest.raw == b_nest.raw),
                ),
                z3.Or(
                    z3.Not((a_nest.raw == b_nest.raw)),
                    (a_nest.input_ == b_nest.input_).raw,
                ),
            )
        else:
            condition = z3.And(
                condition,
                z3.Or(
                    z3.Not((a_nest.input_ != b_nest.input_).raw),
                    (a_nest.raw == b_nest.raw),
                ),
                z3.Or(
                    z3.Not((a_nest.raw == b_nest.raw)),
                    (a_nest.input_ != b_nest.input_).raw,
                ),
            )

    comparision = And(
        Bool(cast(z3.BoolRef, operation(a.raw, b.raw)), annotations=union),
        Bool(condition) if b.nested_functions else Bool(True),
        a.input_ == b.input_ if inputs_equal else a.input_ != b.input_,
    )
    if a.potential_value:
        for i, val in enumerate(a.potential_value):
            comparision = Or(comparision, And(operation(val[0].raw, b.raw), val[1]))

    comparision.simplify()
    return comparision


class BitVecFunc(BitVec):
    """A bit vector function symbol. Used in place of functions like sha3."""

    def __init__(
        self,
        raw: z3.BitVecRef,
        func_name: Optional[str],
        input_: "BitVec" = None,
        annotations: Optional[Annotations] = None,
        nested_functions: Optional[List["BitVecFunc"]] = None,
        concat_args: List = None,
    ):
        """

        :param raw: The raw bit vector symbol
        :param func_name: The function name. e.g. sha3
        :param input: The input to the functions
        :param annotations: The annotations the BitVecFunc should start with
        """

        self.func_name = func_name
        self.input_ = input_
        self.nested_functions = nested_functions or []
        self.nested_functions = list(dict.fromkeys(self.nested_functions))
        self.concat_args = concat_args or []
        if isinstance(input_, BitVecFunc):
            self.nested_functions.extend(input_.nested_functions)
        super().__init__(raw, annotations)

    def __add__(self, other: Union[int, "BitVec"]) -> "BitVecFunc":
        """Create an addition expression.

        :param other: The int or BitVec to add to this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.add)

    def __sub__(self, other: Union[int, "BitVec"]) -> "BitVecFunc":
        """Create a subtraction expression.

        :param other: The int or BitVec to subtract from this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.sub)

    def __mul__(self, other: "BitVec") -> "BitVecFunc":
        """Create a multiplication expression.

        :param other: The int or BitVec to multiply to this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.mul)

    def __truediv__(self, other: "BitVec") -> "BitVecFunc":
        """Create a signed division expression.

        :param other: The int or BitVec to divide this BitVecFunc by
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.truediv)

    def __and__(self, other: Union[int, "BitVec"]) -> "BitVecFunc":
        """Create an and expression.

        :param other: The int or BitVec to and with this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.and_)

    def __or__(self, other: Union[int, "BitVec"]) -> "BitVecFunc":
        """Create an or expression.

        :param other: The int or BitVec to or with this BitVecFunc
        :return: The resulting BitVecFunc
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return _arithmetic_helper(self, other, operator.or_)

    def __xor__(self, other: Union[int, "BitVec"]) -> "BitVecFunc":
        """Create a xor expression.

        :param other: The int or BitVec to xor with this BitVecFunc
        :return: The resulting BitVecFunc
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return _arithmetic_helper(self, other, operator.xor)

    def __lt__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed less than expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return _comparison_helper(
            self, other, operator.lt, default_value=False, inputs_equal=False
        )

    def __gt__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed greater than expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return _comparison_helper(
            self, other, operator.gt, default_value=False, inputs_equal=False
        )

    def __le__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed less than or equal to expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return Or(self < other, self == other)

    def __ge__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed greater than or equal to expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return Or(self > other, self == other)

    # MYPY: fix complains about overriding __eq__
    def __eq__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an equality expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """

        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))

        return _comparison_helper(
            self, other, operator.eq, default_value=False, inputs_equal=True
        )

    # MYPY: fix complains about overriding __ne__
    def __ne__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an inequality expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        return _comparison_helper(
            self, other, operator.ne, default_value=True, inputs_equal=False
        )

    def __lshift__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """
        Left shift operation
        :param other: The int or BitVec to shift on
        :return The resulting left shifted output
        """
        return _arithmetic_helper(self, other, operator.lshift)

    def __rshift__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """
        Right shift operation
        :param other: The int or BitVec to shift on
        :return The resulting right shifted output:
        """
        return _arithmetic_helper(self, other, operator.rshift)

    def __hash__(self) -> int:
        return self.raw.__hash__()


class BitVecFuncExtract(BitVecFunc):
    """A bit vector function wrapper, useful for preserving Extract() and Concat() operations"""

    def __init__(
        self,
        raw: z3.BitVecRef,
        func_name: Optional[str],
        input_: "BitVec" = None,
        annotations: Optional[Annotations] = None,
        nested_functions: Optional[List["BitVecFunc"]] = None,
        concat_args: List = None,
        low=None,
        high=None,
        parent=None,
    ):
        """

        :param raw: The raw bit vector symbol
        :param func_name: The function name. e.g. sha3
        :param input: The input to the functions
        :param annotations: The annotations the BitVecFunc should start with
        """
        super().__init__(
            raw=raw,
            func_name=func_name,
            input_=input_,
            annotations=annotations,
            nested_functions=nested_functions,
            concat_args=concat_args,
        )
        self.low = low
        self.high = high
        self.parent = parent
