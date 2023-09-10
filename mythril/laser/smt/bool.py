"""This module provides classes for an SMT abstraction of boolean
expressions."""

from typing import Union, cast, Set

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
                        self.annotations.union(other.annotations))
        return Bool(cast(z3.BoolRef, self.raw == other), self.annotations)

    # MYPY: complains about overloading __ne__ # noqa
    def __ne__(self, other: object) -> "Bool":  # type: ignore
        """

        :param other:
        :return:
        """
        if isinstance(other, Expression):
            return Bool(cast(z3.BoolRef, self.raw != other.raw),
                        self.annotations.union(other.annotations))
        return Bool(cast(z3.BoolRef, self.raw != other), self.annotations)

    def __bool__(self) -> bool:
        """

        :return:
        """
        if self.value is not None:
            return self.value
        else:
            return False

    def substitute(self, original_expression, new_expression):
        """

        :param original_expression:
        :param new_expression:
        """
        if self.raw is None:
            return
        original_z3 = original_expression.raw
        new_z3 = new_expression.raw
        self.raw = z3.substitute(self.raw, (original_z3, new_z3))

    def __hash__(self) -> int:
        return self.raw.__hash__()


def And(*args: Union[Bool, bool]) -> Bool:
    """Create an And expression."""
    annotations: Set = set()
    args_list = [arg if isinstance(arg, Bool) else Bool(arg) for arg in args]
    for arg in args_list:
        annotations = annotations.union(arg.annotations)
    return Bool(z3.And([a.raw for a in args_list]), annotations)


def Xor(a: Bool, b: Bool) -> Bool:
    """Create an And expression."""

    union = a.annotations.union(b.annotations)
    return Bool(z3.Xor(a.raw, b.raw), union)


def Or(*args: Union[Bool, bool]) -> Bool:
    """Create an or expression.

    :param a:
    :param b:
    :return:
    """
    args_list = [arg if isinstance(arg, Bool) else Bool(arg) for arg in args]
    annotations: Set = set()
    for arg in args_list:
        annotations = annotations.union(arg.annotations)
    return Bool(z3.Or([a.raw for a in args_list]), annotations=annotations)


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
