"""This module contains the class used to represent state-change constraints in
the call graph."""
from mythril.exceptions import UnsatError, SolverTimeOutException
from mythril.laser.smt import symbol_factory, simplify, Bool
from mythril.support.model import get_model
from mythril.laser.ethereum.function_managers import keccak_function_manager

from copy import copy
from typing import Iterable, List, Optional, Union


class Constraints(list):
    """This class should maintain a solver and it's constraints, This class
    tries to make the Constraints() object as a simple list of constraints with
    some background processing.

    """

    def __init__(self, constraint_list: Optional[List[Bool]] = None) -> None:
        """

        :param constraint_list: List of constraints
        """
        constraint_list = constraint_list or []
        constraint_list = self._get_smt_bool_list(constraint_list)
        super(Constraints, self).__init__(constraint_list)

    def is_possible(self, solver_timeout=None) -> bool:
        """
        :param solver_timeout: The default timeout uses analysis timeout from args.solver_timeout
        :return: True/False based on the existence of solution of constraints
        """
        try:
            get_model(self, solver_timeout=solver_timeout)
        except SolverTimeOutException:
            # If it uses the long analysis solver timeout
            if solver_timeout is None:
                return False
            # If it uses a short custom solver timeout
            return True
        except UnsatError:
            return False
        return True

    def get_model(self, solver_timeout=None) -> bool:
        """
        :param solver_timeout: The default timeout uses analysis timeout from args.solver_timeout
        :return: True/False based on the existence of solution of constraints
        """
        try:
            return get_model(self, solver_timeout=solver_timeout)
        except SolverTimeOutException:
            return None
        except UnsatError:
            return None

    def append(self, constraint: Union[bool, Bool]) -> None:
        """

        :param constraint: The constraint to be appended
        """
        constraint = (
            simplify(constraint)
            if isinstance(constraint, Bool)
            else symbol_factory.Bool(constraint)
        )
        super(Constraints, self).append(constraint)

    @property
    def as_list(self) -> List[Bool]:
        """
        :return: returns the list of constraints
        """
        return self[:] + [keccak_function_manager.create_conditions()]

    def __copy__(self) -> "Constraints":
        """

        :return: The copied constraint List
        """
        constraint_list = super(Constraints, self).copy()
        return Constraints(constraint_list)

    def copy(self) -> "Constraints":
        return self.__copy__()

    def __deepcopy__(self, memodict=None) -> "Constraints":
        """

        :param memodict:
        :return: The copied constraint List
        """
        new_constraints = Constraints()
        for constraint in self:
            new_constraints.append(copy(constraint))
        return new_constraints

    def __add__(self, constraints: List[Union[bool, Bool]]) -> "Constraints":
        """

        :param constraints:
        :return: the new list after the + operation
        """
        constraints_list = self._get_smt_bool_list(constraints)
        constraints_list = super(Constraints, self).__add__(constraints_list)
        return Constraints(constraint_list=constraints_list)

    def __iadd__(self, constraints: Iterable[Union[bool, Bool]]) -> "Constraints":
        """

        :param constraints:
        :return:
        """
        list_constraints = self._get_smt_bool_list(constraints)
        super(Constraints, self).__iadd__(list_constraints)
        return self

    @staticmethod
    def _get_smt_bool_list(constraints: Iterable[Union[bool, Bool]]) -> List[Bool]:
        return [
            constraint
            if isinstance(constraint, Bool)
            else symbol_factory.Bool(constraint)
            for constraint in constraints
        ]

    def get_all_constraints(self):
        return self[:] + [keccak_function_manager.create_conditions()]

    def __hash__(self):
        return tuple(self[:]).__hash__()
