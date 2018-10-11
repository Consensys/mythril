from typing import Any
from z3 import ExprRef


class Types:
    #: Constraints, formulas and items are constraint expressions.
    Expr = ExprRef


class NotConcreteValueError(Exception):
    """
    Raise if no concrete value can be got.
    """

    def __init__(self, expr: Any):
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
