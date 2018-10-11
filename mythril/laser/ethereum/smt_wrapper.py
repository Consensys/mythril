from z3 import ExprRef, is_bv
from z3 import simplify as z3_simplify


class Types:
    #: Constraints, formulas and items are constraint expressions.
    Expr = ExprRef


def get_concrete_value(expr: Types.Expr):
    """
    Get the concrete value of a constraint expression `expr`

    :param expr: the constraint expression

    :return: the concrete value of `expr`

    :raise TypeError: if `expr` is not a concrete value
    """
    try:
        return expr.as_long()
    except AttributeError:
        pass
    raise TypeError("{} is not concrete value".format(expr))


def Eq(lhs, rhs) -> Types.Expr:
    """
    Make an equation formula `lhs == rhs`

    :param lhs: the left side of the equation formula
    :param rhs: the right side of the equation formula

    :return: a formula `lhs == rhs`
    """
    return lhs == rhs


def Neq(lhs, rhs) -> Types.Expr:
    """
    Make an inequation formula `lhs <> rhs`

    :param lhs: the left side of the inequation formula
    :param rhs: the right side of the inequation formula

    :return: a formula `lhs <> rhs`
    """
    return lhs != rhs


def SLT(lhs, rhs) -> Types.Expr:
    """
    Make a signed less-than comparison `lhs < rhs`

    :param lhs: the left side of the comparison
    :param rhs: the right side of the comparison

    :return: a signed less-than comparison `lhs < rhs`

    :raise TypeError: if none of them is the bit vector
    """

    if not (is_bv(lhs) or is_bv(rhs)):
        raise TypeError

    return lhs < rhs


def SGT(lhs, rhs) -> Types.Expr:
    """
    Make a signed greater-than comparison `lhs > rhs`, or a shortcut formula
    True or False.

    :param lhs: the left side of the comparison
    :param rhs: the right side of the comparison

    :return: a signed greater-than comparison `lhs > rhs`

    :raise TypeError: if none of them is the bit vector
    """

    if not (is_bv(lhs) or is_bv(rhs)):
        raise TypeError

    return lhs > rhs


def SDiv(dividend, divisor) -> Types.Expr:
    """
    Make a signed division `dividend / divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: a signed division `dividend / divisor`

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    if not (is_bv(dividend) or is_bv(divisor)):
        raise TypeError

    return dividend / divisor


class SimplificationError(Exception):
    """
    Raise if the simplification fails.
    """

    def __init__(self, reason):
        self.reason = reason


def simplify(expr: Types.Expr) -> Types.Expr:
    """
    Simplify the constrain expression `expr`.

    :param expr: the expression to be simplified

    :return: the simplified form of `expr`

    :raise SimplificationError: if any error occurs
    """

    try:
        return z3_simplify(expr)
    except Exception as e:
        reason = str(e)
    raise SimplificationError(reason)
