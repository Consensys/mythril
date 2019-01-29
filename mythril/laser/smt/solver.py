"""This module contains an abstract SMT representation of an SMT solver."""
import z3
from typing import Union, cast, TypeVar, Generic, List, Sequence

from mythril.laser.smt.expression import Expression
from mythril.laser.smt.bool import Bool


T = TypeVar("T", bound=Union[z3.Solver, z3.Optimize])


class BaseSolver(Generic[T]):
    def __init__(self, raw: T) -> None:
        """"""
        self.raw = raw

    def set_timeout(self, timeout: int) -> None:
        """Sets the timeout that will be used by this solver, timeout is in
        milliseconds.

        :param timeout:
        """
        assert timeout > 0  # timeout <= 0 isn't supported by z3
        self.raw.set(timeout=timeout)

    def add(self, constraints: Union[Bool, List[Bool]]) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        if not isinstance(constraints, list):
            self.raw.add(constraints.raw)
            return
        z3_constraints = [c.raw for c in constraints]  # type: Sequence[z3.BoolRef]
        self.raw.add(z3_constraints)

    def append(self, constraints: Union[Bool, List[Bool]]) -> None:
        """Adds the constraints to this solver.

        :param constraints:
        :return:
        """
        self.add(constraints)

    def check(self) -> z3.CheckSatResult:
        """Returns z3 smt check result.

        :return:
        """
        return self.raw.check()

    def model(self) -> z3.ModelRef:
        """Returns z3 model for a solution.

        :return:
        """
        return self.raw.model()


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
