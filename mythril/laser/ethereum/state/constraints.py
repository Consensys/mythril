"""This module contains the class used to represent state-change constraints in
the call graph."""

from mythril.laser.smt import Solver, Bool

from typing import List, Optional
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
        super(Constraints, self).__init__(constraint_list or [])
        self.__default_timeout = 10
        self.__is_possible = is_possible

    def check_possibility(self) -> bool:
        """
        :return: True/False based on the existence of solution of constraints
        """
        if self.__is_possible is not None:
            return self.__is_possible
        solver = Solver()
        solver.set_timeout(self.__default_timeout)
        for constraint in self[:]:
            solver.add(constraint)
        self.__is_possible = solver.check() != unsat
        return self.__is_possible

    def append(self, constraint: Bool) -> None:
        """

        :param constraint: The constraint to be appended
        """
        super(Constraints, self).append(constraint)
        self.__is_possible = None

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
        return Constraints(constraint_list, is_possible=self.__is_possible)

    def __deepcopy__(self, memodict=None) -> "Constraints":
        """

        :param memodict:
        :return: The copied constraint List
        """
        return self.__copy__()

    def __add__(self, constraints: List[Bool]) -> "Constraints":
        """

        :param constraints:
        :return: the new list after the + operation
        """
        constraints_list = super(Constraints, self).__add__(constraints)
        return Constraints(constraint_list=constraints_list, is_possible=None)

    def __iadd__(self, constraints: List[Bool]) -> "Constraints":
        """

        :param constraints:
        :return:
        """
        super(Constraints, self).__iadd__(constraints)
        self.__is_possible = None
        return self
