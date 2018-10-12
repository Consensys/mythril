from z3 import ExprRef, is_bv


class Types:
    #: Constraints, formulas and items are constraint expressions.
    Expr = ExprRef


class NotConcreteValueError(Exception):
    """
    Raise if no concrete value can be got.
    """

    def __init__(self, expr):
        self.expr = expr


def get_concrete_value(expr: Types.Expr):
    """
    Get the concrete value of a constraint expression `expr`

    :param expr: the constraint expression

    :return: the concrete value of `expr`

    :raise NotConcreteValueError: if `expr` is not a concrete value
    """
    try:
        return expr.as_long()
    except AttributeError:
        pass
    raise NotConcreteValueError(expr)


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
