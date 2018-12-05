import z3

from mythril.laser.smt.expression import Expression

# fmt: off


class Bool(Expression):

    @property
    def is_false(self):
        return z3.is_false(self.raw)

    @property
    def is_true(self):
        return z3.is_true(self.raw)

