from typing import cast, List, Any, Set
import z3

from mythril.laser.smt.bitvec import BitVec


class Function:
    """An uninterpreted function."""

    def __init__(self, name: str, domain: List[int], value_range: int):
        """Initializes an uninterpreted function.

        :param name: Name of the Function
        :param domain: The domain for the Function (10 -> all the values that a bv of size 10 could take)
        :param value_range: The range for the values of the function (10 -> all the values that a bv of size 10 could take)
        """
        self.domain = []
        for element in domain:
            self.domain.append(z3.BitVecSort(element))
        self.range = z3.BitVecSort(value_range)
        self.raw = z3.Function(name, *self.domain, self.range)

    def __call__(self, *items) -> BitVec:
        """Function accessor, item can be symbolic."""
        annotations: Set[Any] = set().union(*[item.annotations for item in items])
        return BitVec(
            cast(z3.BitVecRef, self.raw(*[item.raw for item in items])),
            annotations=annotations,
        )
