from typing import cast
import z3

from mythril.laser.smt.bitvec import BitVec


class Function:
    """An uninterpreted function."""

    def __init__(self, name: str, domain: int, value_range: int):
        """Initializes an uninterpreted function.

        :param name: Name of the Function
        :param domain: The domain for the Function (10 -> all the values that a bv of size 10 could take)
        :param value_range: The range for the values of the function (10 -> all the values that a bv of size 10 could take)
        """
        self.domain = z3.BitVecSort(domain)
        self.range = z3.BitVecSort(value_range)
        self.raw = z3.Function(name, self.domain, self.range)

    def __call__(self, item: BitVec) -> BitVec:
        """Function accessor, item can be symbolic."""
        return BitVec(
            cast(z3.BitVecRef, self.raw(item.raw)), annotations=item.annotations
        )  # type: ignore
