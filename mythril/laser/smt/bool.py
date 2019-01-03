"""This module provides classes for an SMT abstraction of boolean
expressions."""

from typing import Union

import z3

from mythril.laser.smt.expression import Expression


# fmt: off


class Bool(Expression):
    """This is a Bool expression."""

    @property
    def is_false(self) -> bool:
        """Specifies whether this variable can be simplified to false.

        :return:
        """
        self.simplify()
        return z3.is_false(self.raw)

    @property
    def is_true(self) -> bool:
        """Specifies whether this variable can be simplified to true.

        :return:
        """
        self.simplify()
        return z3.is_true(self.raw)

    @property
    def value(self) -> Union[bool, None]:
        """Returns the concrete value of this bool if concrete, otherwise None.

        :return: Concrete value or None
        """
        self.simplify()
        if self.is_true:
            return True
        elif self.is_false:
            return False
        else:
            return None

    def __eq__(self, other):
        """

        :param other:
        :return:
        """
        if isinstance(other, Expression):
            return Bool(self.raw == other.raw, self.annotations + other.annotations)
        return Bool(self.raw == other, self.annotations)

    def __ne__(self, other):
        """

        :param other:
        :return:
        """
        if isinstance(other, Expression):
            return Bool(self.raw != other.raw, self.annotations + other.annotations)
        return Bool(self.raw != other, self.annotations)

    def __bool__(self):
        """

        :return:
        """
        if self.value is not None:
            return self.value
        else:
            return False


def Or(a: Bool, b: Bool):
    """Create an or expression.

    :param a:
    :param b:
    :return:
    """
    union = a.annotations + b.annotations
    return Bool(z3.Or(a.raw, b.raw), annotations=union)


def Not(a: Bool):
    """Create a Not expression.

    :param a:
    :return:
    """
    return Bool(z3.Not(a.raw), a.annotations)


def is_false(a: Bool) -> bool:
    """Returns whether the provided bool can be simplified to false.

    :param a:
    :return:
    """
    return z3.is_false(a.raw)


def is_true(a: Bool) -> bool:
    """Returns whether the provided bool can be simplified to true.

    :param a:
    :return:
    """
    return z3.is_true(a.raw)
