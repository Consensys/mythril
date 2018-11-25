from z3 import Solver, unsat
from copy import copy


class Constraints(list):
    """
    This class should maintain a solver and it's constraints, This class tries to make the Constraints() object
    as a simple list of constraints with some background processing.
    TODO: add the solver to this class after callback refactor
    """

    def __init__(self, constraint_list=None, solver=None, possibility=None):
        super(Constraints, self).__init__(constraint_list or [])
        self.solver = solver or Solver()
        self.solver.set("timeout", 1)
        self.__possibility = possibility

    def check_possibility(self):
        if self.__possibility is None:
            self.__possibility = (self.solver.check() != unsat)
        if self.__possibility is False:
            self.solver = None
        return self.__possibility

    def append(self, constraint):
        self.__possibility = None
        super(Constraints, self).append(constraint)
        if self.solver is not None:
            self.solver.add(constraint)

    def pop(self, index=-1):
        raise NotImplementedError

    def __copy__(self):
        constraint_list = super(Constraints, self).copy()
        if self.solver is not None:
            solver = copy(self.solver)
        else:
            solver = None
        return Constraints(constraint_list, solver)

    def __deepcopy__(self, memodict=None):
        return self.__copy__()

    def __add__(self, constraints):
        constraints_list = super(Constraints, self).__add__(constraints)
        if self.solver is not None:
            solver = copy(self.solver)
            for constraint in constraints:
                solver.add(constraint)
        else:
            solver = None
        return Constraints(constraint_list=constraints_list, solver=solver)

    def __iadd__(self, constraints):
        super(Constraints, self).__iadd__(constraints)
        if self.solver is None:
            return self
        for constraint in constraints:
            self.solver.add(constraint)
        return self
