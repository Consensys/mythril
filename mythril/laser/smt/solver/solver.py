"""This module contains an abstract SMT representation of an SMT solver."""
import logging
import os
import sys
import z3
from typing import Union, cast, TypeVar, Generic, List, Sequence

from mythril.laser.smt.expression import Expression
from mythril.laser.smt.model import Model
from mythril.laser.smt.bool import Bool
from mythril.laser.smt.solver.solver_statistics import stat_smt_query

T = TypeVar("T", bound=Union[z3.Solver, z3.Optimize])

log = logging.getLogger(__name__)


class BaseSolver(Generic[T]):
    def __init__(self, raw: T) -> None:
        """"""
        self.raw = raw

    def set_timeout(self, timeout: int) -> None:
        """Sets the timeout that will be used by this solver, timeout is in
        milliseconds.

        :param timeout:
        """
        self.raw.set(timeout=timeout)

    def add(self, *constraints: List[Bool]) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        z3_constraints = [
            c.raw for c in cast(List[Bool], constraints)
        ]  # type: Sequence[z3.BoolRef]
        self.raw.add(z3_constraints)

    def append(self, *constraints: List[Bool]) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        self.add(*constraints)

    @stat_smt_query
    def check(self, *args) -> z3.CheckSatResult:
        """Returns z3 smt check result.
        Also suppresses the stdout when running z3 library's check() to avoid unnecessary output
        :return: The evaluated result which is either of sat, unsat or unknown
        """
        old_stdout = sys.stdout
        with open(os.devnull, "w") as dev_null_fd:
            sys.stdout = dev_null_fd
            try:
                evaluate = self.raw.check(args)
            except z3.z3types.Z3Exception as e:
                # Some requests crash the solver
                evaluate = z3.unknown
                log.info(f"Encountered Z3 exception when checking the constraints: {e}")
        sys.stdout = old_stdout
        return evaluate

    def model(self) -> Model:
        """Returns z3 model for a solution.

        :return:
        """
        try:
            return Model([self.raw.model()])
        except z3.z3types.Z3Exception as e:
            log.info(f"Encountered a Z3 exception while querying for the model: {e}")
            return Model()

    def sexpr(self):
        return self.raw.sexpr()


class Solver(BaseSolver[z3.Solver]):
    """An SMT solver object."""

    def __init__(self) -> None:
        """"""
        super().__init__(z3.Solver())

    def reset(self) -> None:
        """Reset this solver."""
        self.raw.reset()

    def pop(self, num: int) -> None:
        """Pop num constraints from this solver.

        :param num:
        """
        self.raw.pop(num)


class Optimize(BaseSolver[z3.Optimize]):
    """An optimizing smt solver."""

    def __init__(self) -> None:
        """Create a new optimizing solver instance."""
        super().__init__(z3.Optimize())

    def minimize(self, element: Expression[z3.ExprRef]) -> None:
        """In solving this solver will try to minimize the passed expression.

        :param element:
        """
        self.raw.minimize(element.raw)

    def maximize(self, element: Expression[z3.ExprRef]) -> None:
        """In solving this solver will try to maximize the passed expression.

        :param element:
        """
        self.raw.maximize(element.raw)
