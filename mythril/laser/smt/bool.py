import z3

from mythril.laser.smt.expression import Expression

# fmt: off


class Bool(Expression):

    @property
    def is_false(self) -> bool:
        return z3.is_false(self.raw)

    @property
    def is_true(self) -> bool:
        return z3.is_true(self.raw)


def is_false(a: Bool) -> bool:
    return is_false(a)


def is_true(a: Bool) -> bool:
    return is_true(a)
