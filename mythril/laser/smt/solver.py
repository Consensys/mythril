import z3
from mythril.laser.smt.bool import Bool


class Solver:
    """
    An smt solver object
    """

    def __init__(self):
        self.raw = z3.Solver()

    def set_timeout(self, timeout) -> None:
        """ Sets the timeout that will be used by this solver"""
        self.raw.set(timeout=timeout)

    def add(self, constraints: list[Bool]) -> None:
        """ Adds the constraints to this solver """
        constraints = [c.raw for c in constraints]
        self.raw.add(constraints)

    def append(self, constraints: list[Bool]) -> None:
        """ Adds the constraints to this solver """
        constraints = [c.raw for c in constraints]
        self.raw.add(constraints)

    def check(self):
        return self.raw.check()

    def model(self):
        return self.raw.model()

    def reset(self) -> None:
        self.raw.reset()

    def pop(self, num) -> None:
        self.raw.pop(num)
