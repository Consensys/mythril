"""This module provides classes for an SMT abstraction of boolean
expressions."""

from typing import Union, cast, List

import z3

from mythril.laser.smt.expression import Expression


# fmt: off


class Bool(Expression[z3.BoolRef]):
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

    # MYPY: complains about overloading __eq__ # noqa
    def __eq__(self, other: object) -> "Bool":  # type: ignore
        """

        :param other:
        :return:
        """
        if isinstance(other, Expression):
            return Bool(cast(z3.BoolRef, self.raw == other.raw),
                        self.annotations + other.annotations)
        return Bool(cast(z3.BoolRef, self.raw == other), self.annotations)

    # MYPY: complains about overloading __ne__ # noqa
    def __ne__(self, other: object) -> "Bool":  # type: ignore
        """

        :param other:
        :return:
        """
        if isinstance(other, Expression):
            return Bool(cast(z3.BoolRef, self.raw != other.raw),
                        self.annotations + other.annotations)
        return Bool(cast(z3.BoolRef, self.raw != other), self.annotations)

    def __bool__(self) -> bool:
        """

        :return:
        """
        if self.value is not None:
            return self.value
        else:
            return False

    def __hash__(self):
        return self.raw.__hash__()


def And(*args: Union[Bool, bool]) -> Bool:
    """Create an And expression."""
    union = []
    args_list = [arg if isinstance(arg, Bool) else Bool(arg) for arg in args]
    for arg in args_list:
        union.append(arg.annotations)
    return Bool(z3.And([a.raw for a in args_list]), union)


def Or(*args: Union[Bool, bool]) -> Bool:
    """Create an or expression.

    :param a:
    :param b:
    :return:
    """
    args_list = [arg if isinstance(arg, Bool) else Bool(arg) for arg in args]
    union = [arg.annotations for arg in args_list]
    return Bool(z3.Or([a.raw for a in args_list]), annotations=union)


def Not(a: Bool) -> Bool:
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
