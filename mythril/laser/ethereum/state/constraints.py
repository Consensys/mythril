"""This module contains the class used to represent state-change constraints in
the call graph."""

from mythril.laser.smt import Solver, Bool, symbol_factory, simplify

from typing import Iterable, List, Optional, Union
from z3 import unsat


class Constraints(list):
    """This class should maintain a solver and it's constraints, This class
    tries to make the Constraints() object as a simple list of constraints with
    some background processing.

    """

    def __init__(
        self,
        constraint_list: Optional[List[Bool]] = None,
        is_possible: Optional[bool] = None,
    ) -> None:
        """

        :param constraint_list: List of constraints
        :param is_possible: Whether it is possible to satisfy the constraints or not
        """
        constraint_list = constraint_list or []
        constraint_list = self._get_smt_bool_list(constraint_list)
        super(Constraints, self).__init__(constraint_list)
        self._default_timeout = 100
        self._is_possible = is_possible

    @property
    def is_possible(self) -> bool:
        """
        :return: True/False based on the existence of solution of constraints
        """
        if self._is_possible is not None:
            return self._is_possible
        solver = Solver()
        solver.set_timeout(self._default_timeout)
        for constraint in self[:]:
            constraint = (
                symbol_factory.Bool(constraint)
                if isinstance(constraint, bool)
                else constraint
            )
            solver.add(constraint)
        self._is_possible = solver.check() != unsat
        return self._is_possible

    def append(self, constraint: Union[bool, Bool]) -> None:
        """

        :param constraint: The constraint to be appended
        """
        constraint = (
            simplify(constraint) if isinstance(constraint, Bool) else Bool(constraint)
        )
        super(Constraints, self).append(constraint)
        self._is_possible = None

    def pop(self, index: int = -1) -> None:
        """

        :param index: Index to be popped from the list
        """
        raise NotImplementedError

    @property
    def as_list(self) -> List[Bool]:
        """
        :return: returns the list of constraints
        """
        return self[:]

    def __copy__(self) -> "Constraints":
        """

        :return: The copied constraint List
        """
        constraint_list = super(Constraints, self).copy()
        return Constraints(constraint_list, is_possible=self._is_possible)

    def copy(self) -> "Constraints":
        return self.__copy__()

    def __deepcopy__(self, memodict=None) -> "Constraints":
        """

        :param memodict:
        :return: The copied constraint List
        """
        return self.__copy__()

    def __add__(self, constraints: List[Union[bool, Bool]]) -> "Constraints":
        """

        :param constraints:
        :return: the new list after the + operation
        """
        constraints_list = self._get_smt_bool_list(constraints)
        constraints_list = super(Constraints, self).__add__(constraints_list)
        return Constraints(constraint_list=constraints_list, is_possible=None)

    def __iadd__(self, constraints: Iterable[Union[bool, Bool]]) -> "Constraints":
        """

        :param constraints:
        :return:
        """
        constraints = self._get_smt_bool_list(constraints)
        super(Constraints, self).__iadd__(constraints)
        self._is_possible = None
        return self

    @staticmethod
    def _get_smt_bool_list(constraints: Iterable[Union[bool, Bool]]) -> List[Bool]:
        return [
            constraint if isinstance(constraint, Bool) else Bool(constraint)
            for constraint in constraints
        ]

    def __hash__(self):
        return tuple(self[:]).__hash__()
