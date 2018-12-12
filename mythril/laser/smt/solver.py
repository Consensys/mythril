import z3
from mythril.laser.smt.bool import Bool
from mythril.laser.smt.expression import Expression


class Solver:
    """
    An smt solver object
    """

    def __init__(self):
        self.raw = z3.Solver()

    def set_timeout(self, timeout) -> None:
        """ Sets the timeout that will be used by this solver"""
        self.raw.set(timeout=timeout)

    def add(self, constraints: list) -> None:
        """ Adds the constraints to this solver """
        if not isinstance(constraints, list):
            self.raw.add(constraints.raw)
            return
        constraints = [c.raw for c in constraints]
        self.raw.add(constraints)

    def append(self, constraints: list) -> None:
        """ Adds the constraints to this solver """
        if not isinstance(constraints, list):
            self.raw.append(constraints.raw)
            return
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


class Optimize(Solver):
    def __init__(self):
        super().__init__()
        self.raw = z3.Optimize()

    def minimize(self, element: Expression):
        self.raw.minimize(element.raw)

    def maximize(self, element: Expression):
        self.raw.maximize(element.raw)
