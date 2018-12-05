import z3
from typing import Union

from mythril.laser.smt.expression import Expression

# fmt: off


class Bool(Expression):
    """
    This is a Bool expression
    """

    @property
    def is_false(self) -> bool:
        """ Specifies whether this variable can be simplified to false"""
        self.simplify()
        return z3.is_false(self.raw)

    @property
    def is_true(self) -> bool:
        """ Specifies whether this variable can be simplified to true"""
        self.simplify()
        return z3.is_true(self.raw)

    @property
    def value(self) -> Union[bool, None]:
        """ Returns the concrete value of this bool if concrete, otherwise None"""
        if self.is_true:
            return True
        elif self.is_false:
            return False
        else:
            return None


def is_false(a: Bool) -> bool:
    """ Returns whether the provided bool can be simplified to false"""
    return is_false(a)


def is_true(a: Bool) -> bool:
    """ Returns whether the provided bool can be simplified to true"""
    return is_true(a)
