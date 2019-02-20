from typing import Optional, Union, cast, Callable

import z3

from mythril.laser.smt.bitvec import BitVec, Bool, And, Annotations
from mythril.laser.smt.bool import Or

import operator


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
    union = a.annotations + b.annotations

    if isinstance(b, BitVecFunc):
        # TODO: Find better value to set input and name to in this case?
        return BitVecFunc(raw=raw, func_name=None, input_=None, annotations=union)

    return BitVecFunc(
        raw=raw, func_name=a.func_name, input_=a.input_, annotations=union
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

    union = a.annotations + b.annotations

    if not a.symbolic and not b.symbolic:
        return Bool(z3.BoolVal(operation(a.value, b.value)), annotations=union)

    if (
        not isinstance(b, BitVecFunc)
        or not a.func_name
        or not a.input_
        or not a.func_name == b.func_name
    ):
        return Bool(z3.BoolVal(default_value), annotations=union)

    return And(
        Bool(cast(z3.BoolRef, operation(a.raw, b.raw)), annotations=union),
        a.input_ == b.input_ if inputs_equal else a.input_ != b.input_,
    )


class BitVecFunc(BitVec):
    """A bit vector function symbol. Used in place of functions like sha3."""

    def __init__(
        self,
        raw: z3.BitVecRef,
        func_name: Optional[str],
        input_: Union[int, "BitVec"] = None,
        annotations: Optional[Annotations] = None,
    ):
        """

        :param raw: The raw bit vector symbol
        :param func_name: The function name. e.g. sha3
        :param input: The input to the functions
        :param annotations: The annotations the BitVecFunc should start with
        """

        self.func_name = func_name
        self.input_ = input_
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

    def __or__(self, other: "BitVec") -> "BitVecFunc":
        """Create an or expression.

        :param other: The int or BitVec to or with this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.or_)

    def __xor__(self, other: "BitVec") -> "BitVecFunc":
        """Create a xor expression.

        :param other: The int or BitVec to xor with this BitVecFunc
        :return: The resulting BitVecFunc
        """
        return _arithmetic_helper(self, other, operator.xor)

    def __lt__(self, other: "BitVec") -> Bool:
        """Create a signed less than expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return _comparison_helper(
            self, other, operator.lt, default_value=False, inputs_equal=False
        )

    def __gt__(self, other: "BitVec") -> Bool:
        """Create a signed greater than expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return _comparison_helper(
            self, other, operator.gt, default_value=False, inputs_equal=False
        )

    def __le__(self, other: "BitVec") -> Bool:
        """Create a signed less than or equal to expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return Or(self < other, self == other)

    def __ge__(self, other: "BitVec") -> Bool:
        """Create a signed greater than or equal to expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return Or(self > other, self == other)

    # MYPY: fix complains about overriding __eq__
    def __eq__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an equality expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return _comparison_helper(
            self, other, operator.eq, default_value=False, inputs_equal=True
        )

    # MYPY: fix complains about overriding __ne__
    def __ne__(self, other: Union[int, "BitVec"]) -> Bool:  # type: ignore
        """Create an inequality expression.

        :param other: The int or BitVec to compare to this BitVecFunc
        :return: The resulting Bool
        """
        return _comparison_helper(
            self, other, operator.eq, default_value=True, inputs_equal=False
        )
