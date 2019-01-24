"""This module contains the class used to represent state-change constraints in
the call graph."""

from z3 import Solver, unsat
from copy import copy


class Constraints(list):
    """This class should maintain a solver and it's constraints, This class
    tries to make the Constraints() object as a simple list of constraints with
    some background processing.

    TODO: add the solver to this class after callback refactor
    """

    def __init__(self, constraint_list=None, solver=None, possibility=None):
        """

        :param constraint_list:
        :param solver:
        :param possibility:
        """
        super(Constraints, self).__init__(constraint_list or [])
        self.solver = solver or Solver()
        self.solver.set("timeout", 1)
        self.__possibility = possibility

    def check_possibility(self):
        if self.__possibility is None:
            self.__possibility = self.solver.check() != unsat
        if self.__possibility is False:
            self.solver = None
        return self.__possibility

    def append(self, constraint):
        """

        :param constraint:
        """
        super(Constraints, self).append(constraint)
        if self.solver is not None:
            self.solver.add(constraint.raw)

    def pop(self, index=-1):
        """

        :param index:
        """
        raise NotImplementedError

    def __copy__(self):
        """

        :return:
        """
        constraint_list = super(Constraints, self).copy()
        return Constraints(constraint_list, self.solver)

    def copy_solver(self):
        self.solver = copy(self.solver)

    def __deepcopy__(self, memodict=None):
        """

        :param memodict:
        :return:
        """
        return self.__copy__()

    def __add__(self, constraints):
        """

        :param constraints:
        :return:
        """
        constraints_list = super(Constraints, self).__add__(constraints)
        if self.solver is not None:
            solver = copy(self.solver)
            for constraint in constraints:
                solver.add(constraint.raw)
        else:
            solver = None
        return Constraints(constraint_list=constraints_list, solver=solver)

    def __iadd__(self, constraints):
        """

        :param constraints:
        :return:
        """
        super(Constraints, self).__iadd__(constraints)
        if self.solver is None:
            return self
        for constraint in constraints:
            self.solver.add(constraint.raw)
        return self
