"""This module contains an SMT abstraction of arrays.

This includes an Array class to implement basic store and set
operations, as well as as a K-array, which can be initialized with
default values over a certain range.
"""

from typing import cast
import z3

from mythril.laser.smt.bitvec import BitVec


class BaseArray:
    """Base array type, which implements basic store and set operations."""

    def __init__(self, raw):
        self.raw = raw

    def __getitem__(self, item: BitVec) -> BitVec:
        """Gets item from the array, item can be symbolic."""
        if isinstance(item, slice):
            raise ValueError(
                "Instance of BaseArray, does not support getitem with slices"
            )
        return BitVec(cast(z3.BitVecRef, z3.Select(self.raw, item.raw)))

    def __setitem__(self, key: BitVec, value: BitVec) -> None:
        """Sets an item in the array, key can be symbolic."""
        self.raw = z3.Store(self.raw, key.raw, value.raw)

    def substitute(self, original_expression, new_expression):
        """

        :param original_expression:
        :param new_expression:
        """
        if self.raw is None:
            return
        original_z3 = original_expression.raw
        new_z3 = new_expression.raw
        self.raw = z3.substitute(self.raw, (original_z3, new_z3))


class Array(BaseArray):
    """A basic symbolic array."""

    def __init__(self, name: str, domain: int, value_range: int):
        """Initializes a symbolic array.

        :param name: Name of the array
        :param domain: The domain for the array (10 -> all the values that a bv of size 10 could take)
        :param value_range: The range for the values in the array (10 -> all the values that a bv of size 10 could take)
        """
        self.domain = z3.BitVecSort(domain)
        self.range = z3.BitVecSort(value_range)
        super(Array, self).__init__(z3.Array(name, self.domain, self.range))


class K(BaseArray):
    """A basic symbolic array, which can be initialized with a default
    value."""

    def __init__(self, domain: int, value_range: int, value: int):
        """Initializes an array with a default value.

        :param domain: The domain for the array (10 -> all the values that a bv of size 10 could take)
        :param value_range: The range for the values in the array (10 -> all the values that a bv of size 10 could take)
        :param value: The default value to use for this array
        """
        self.domain = z3.BitVecSort(domain)
        self.value = z3.BitVecVal(value, value_range)
        self.raw = z3.K(self.domain, self.value)
