"""This module contains the class used to represent state-change constraints in the call graph."""


class Constraints(list):
    """
    This class should maintain a solver and it's constraints, This class tries to make the Constraints() object
    as a simple list of constraints with some background processing.
    TODO: add the solver to this class after callback refactor
    """

    def __init__(self, constraint_list=None, solver=None, possibility=None):
        """

        :param constraint_list:
        :param solver:
        :param possibility:
        """
        super(Constraints, self).__init__(constraint_list or [])
        self.solver = solver
        self.__possibility = possibility

    def check_possibility(self):
        """

        :return:
        """
        return True

    def append(self, constraint):
        """

        :param constraint:
        """
        super(Constraints, self).append(constraint)

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
        return Constraints(constraint_list)

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
        return Constraints(constraint_list=constraints_list)

    def __iadd__(self, constraints):
        """

        :param constraints:
        :return:
        """
        super(Constraints, self).__iadd__(constraints)
        return self
