"""This module contains the class used to represent state-change constraints in
the call graph."""

from mythril.laser.smt import Solver
from z3 import unsat


class Constraints(list):
    """This class should maintain a solver and it's constraints, This class
    tries to make the Constraints() object as a simple list of constraints with
    some background processing.

    TODO: add the solver to this class after callback refactor
    """

    def __init__(self, constraint_list=None, possibility=None):
        """

        :param constraint_list:
        :param possibility:
        """
        super(Constraints, self).__init__(constraint_list or [])
        self.__possibility = possibility

    def check_possibility(self):
        if self.__possibility is not None:
            return self.__possibility
        solver = Solver()
        solver.set_timeout(10)
        for constraint in self[:]:
            solver.add(constraint)
        self.__possibility = solver.check() != unsat
        return self.__possibility

    def append(self, constraint):
        """

        :param constraint:
        """
        super(Constraints, self).append(constraint)
        self.__possibility = None

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
        return Constraints(constraint_list, possibility=self.__possibility)

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
        return Constraints(constraint_list=constraints_list, possibility=None)

    def __iadd__(self, constraints):
        """

        :param constraints:
        :return:
        """
        super(Constraints, self).__iadd__(constraints)
        self.__possibility = None
        return self
