"""This module provides classes for an SMT abstraction of bit vectors."""

from operator import lshift, rshift, ne, eq
from typing import Union, Set, cast, Any, Optional, Callable, List

import z3

from mythril.laser.smt.bool import Bool
from mythril.laser.smt.expression import Expression

Annotations = Set[Any]

# fmt: off


def _padded_operation(a: z3.BitVec, b: z3.BitVec, operator):
    if a.size() == b.size():
        return operator(a, b)
    if a.size() < b.size():
        a, b = b, a
    b = z3.Concat(z3.BitVecVal(0, a.size() - b.size()), b)
    return operator(a, b)


class BitVec(Expression[z3.BitVecRef]):
    """A bit vector symbol."""

    def __init__(self, raw: z3.BitVecRef, annotations: Optional[Annotations] = None, concat_args=None, pot_input=True):
        """

        :param raw:
        :param annotations:
        """
        self.concat_args = concat_args or []
        self.potential_values = []
        if pot_input:
            self.potential_input = BitVec(z3.BitVec(str(hash(raw))+"_input", 160), pot_input=False)
            self.potential_input_cond = True
        else:
            self.potential_input = None
            self.potential_input_cond = False
        self.potential_input_dict = {}
        super().__init__(raw, annotations)

    def set_extracted_input_cond(self, high, low, cond):
        self.potential_input_dict[str("{}:{}".format(high, low))] = cond

    def get_extracted_input_cond(self, high, low):
        return self.potential_input_dict.get(str("{}:{}".format(high, low)), False)

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

        union = self.annotations.union(other.annotations)
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

        union = self.annotations.union(other.annotations)
        return BitVec(self.raw - other.raw, annotations=union)

    def __mul__(self, other: "BitVec") -> "BitVec":
        """Create a multiplication expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other * self
        union = self.annotations.union(other.annotations)
        return BitVec(self.raw * other.raw, annotations=union)

    def __truediv__(self, other: "BitVec") -> "BitVec":
        """Create a signed division expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other / self
        union = self.annotations.union(other.annotations)
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
        union = self.annotations.union(other.annotations)
        return BitVec(self.raw & other.raw, annotations=union)

    def __or__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """Create an or expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other | self
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
        return BitVec(self.raw | other.raw, annotations=union)

    def __xor__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """Create a xor expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other ^ self
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
        return BitVec(self.raw ^ other.raw, annotations=union)

    def __lt__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed less than expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other > self
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
        return Bool(self.raw < other.raw, annotations=union)

    def __gt__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed greater than expression.

        :param other:
        :return:
        """
        if isinstance(other, BitVecFunc):
            return other < self
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
        return Bool(self.raw > other.raw, annotations=union)

    def __le__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed less than expression.

        :param other:
        :return:
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
        return Bool(self.raw <= other.raw, annotations=union)

    def __ge__(self, other: Union[int, "BitVec"]) -> Bool:
        """Create a signed greater than expression.

        :param other:
        :return:
        """
        if not isinstance(other, BitVec):
            other = BitVec(z3.BitVecVal(other, self.size()))
        union = self.annotations.union(other.annotations)
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

        union = self.annotations.union(other.annotations)
        # Some of the BitVecs can be 512 bit due to sha3()
        eq_check = _padded_operation(self.raw, other.raw, eq)
        # MYPY: fix complaints due to z3 overriding __eq__
        return Bool(cast(z3.BoolRef, eq_check), annotations=union)

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

        union = self.annotations.union(other.annotations)
        # Some of the BitVecs can be 512 bit due to sha3()
        neq_check = _padded_operation(self.raw, other.raw, ne)
        # MYPY: fix complaints due to z3 overriding __eq__
        return Bool(cast(z3.BoolRef, neq_check), annotations=union)

    def _handle_shift(self, other: Union[int, "BitVec"], operator: Callable) -> "BitVec":
        """
        Handles shift
        :param other: The other BitVector
        :param operator: The shift operator
        :return: the resulting output
        """
        if isinstance(other, BitVecFunc):
            return operator(other, self)
        if not isinstance(other, BitVec):
            return BitVec(
                operator(self.raw, other), annotations=self.annotations
            )
        union = self.annotations.union(other.annotations)
        return BitVec(operator(self.raw, other.raw), annotations=union)

    def __lshift__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """

        :param other:
        :return:
        """
        return self._handle_shift(other, lshift)

    def __rshift__(self, other: Union[int, "BitVec"]) -> "BitVec":
        """

        :param other:
        :return:
        """
        return self._handle_shift(other, rshift)

    def __hash__(self) -> int:
        """

        :return:
        """
        return self.raw.__hash__()


class BitVecExtract(BitVec):
    """A bit vector function wrapper, useful for preserving Extract() and Concat() operations"""

    def __init__(
        self,
        raw: z3.BitVecRef,
        annotations: Optional[Annotations] = None,
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
            annotations=annotations,
            concat_args=concat_args,
        )
        self.low = low
        self.high = high
        self.parent = parent


# TODO: Fix circular import issues
from mythril.laser.smt.bitvecfunc import BitVecFunc
