from z3 import ExprRef
from z3 import simplify as z3_simplify
import z3


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


def is_expr(expr) -> bool:
    """
    Check whether `expr` is a constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a formula; False, otherwise.
    """

    return z3.is_expr(expr)


def is_bv_value(expr) -> bool:
    """
    Check whether `expr` is a concrete bit vector value.

    :param expr: the expression to be checked

    :return: True if `expr` is a concrete bit vector value; False, otherwise.
    """

    return z3.is_bv_value(expr)


def is_bv(expr) -> bool:
    """
    Check whether `expr` is a bit vector.

    :param expr: the expression to be checked

    :return: True if `expr` is a bit vector; False, otherwise.
    """

    return z3.is_bv(expr)


def is_bool(expr) -> bool:
    """
    Check whether `expr` is a boolean constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a boolen constraint expression; False, otherwise.
    """

    return z3.is_bool(expr)


def is_true(expr) -> bool:
    """
    Check whether `expr` is a True constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a True constraint expression; False, otherwise.
    """

    return z3.is_true(expr)


def is_false(expr) -> bool:
    """
    Check whether `expr` is a False constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a False constraint expression; False, otherwise.
    """

    return z3.is_false(expr)


def Not(op) -> Types.Expr:
    """
    Create a Not constraint expression.

    :param op: the operand

    :return: a Not expression
    """

    return z3.Not(op)


def BitVec(name: str, width: int) -> Types.Expr:
    """
    Create a bit vector symbol `name` which is `width` bits wide.

    :param name: the symbol name
    :param width: the number of bits

    :return: a bit vector symbol
    """

    return z3.BitVec(name, width)


def BitVecVal(val: int, width: int) -> Types.Expr:
    """
    Create a bit vector which is `width` bits wide and represent an integer `val`.

    :param val: the value of the bit vector
    :param width: the number of bits of the bit vector

    :return: a bit vector value
    """

    return z3.BitVecVal(val, width)


def Concat(*args) -> Types.Expr:
    """
    Concatenate a sequence of bit vectors.

    :param args: the sequence of bit vectors

    :return: the concatenation of the sequence of bit vectors
    """

    return z3.Concat(*args)


def Extract(last_bit: int, first_bit: int, bv) -> Types.Expr:
    """
    Create an expression that extract bits from `first_bit` to `last_bit`
    (included) from a bit vector `bv`.

    :param last_bit: the last bit (included) to be extracted
    :param first_bit: the first bit to be extracted
    :param bv: the bit vector

    :return: an expression to extract bits
    """

    return z3.Extract(last_bit, first_bit, bv)


def And(*args) -> Types.Expr:
    """
    Create a logical and expression `\\/ *args`.

    :param args: the sub-exprs of the expression

    :return: a logical and expression
    """

    return z3.And(*args)


def Or(*args) -> Types.Expr:
    """
    Create a logical or expression `\\/ *args`.

    :param args: the sub-exprs of the expression

    :return: a logical or expression
    """

    return z3.Or(*args)


def ULT(lhs, rhs) -> Types.Expr:
    """
    Create an unsigned less-than comparison `lhs < rhs`.

    :param lhs: the left operand
    :param rhs: the right operand

    :return: `lhs < rhs`

    :raise TypeError: if none of `lhs` and `rhs` is the bit vector
    """

    if not (is_bv(lhs) or is_bv(rhs)):
        raise TypeError

    return z3.ULT(lhs, rhs)


def UGT(lhs, rhs) -> Types.Expr:
    """
    Create an unsigned greater-than comparison `lhs > rhs`.

    :param lhs: the left operand
    :param rhs: the right operand

    :return: `lhs > rhs`

    :raise TypeError: if none of `lhs` and `rhs` is the bit vector
    """

    if not (is_bv(lhs) or is_bv(rhs)):
        raise TypeError

    return z3.UGT(lhs, rhs)


def If(cond, then_op, else_op) -> Types.Expr:
    """
    Create a if-then-else expression `Ite cond then_op else_op`.

    :param cond: the condition to be checked
    :param then_op: the then operand
    :param else_op: the else operand

    :return: a if-then-else expression
    """

    return z3.If(cond, then_op, else_op)


def UDiv(dividend, divisor) -> Types.Expr:
    """
    Create an unsigned division `dividend / divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: an unsigned division

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    if not (is_bv(dividend) or is_bv(divisor)):
        raise TypeError

    return z3.UDiv(dividend, divisor)


def URem(dividend, divisor) -> Types.Expr:
    """
    Create an unsigned reminder `dividend % divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: an unsigned reminder

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    if not (is_bv(dividend) or is_bv(divisor)):
        raise TypeError

    return z3.URem(dividend, divisor)


def SRem(dividend, divisor) -> Types.Expr:
    """
    Create a signed reminder `dividend % divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: a signed reminder

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    if not (is_bv(dividend) or is_bv(divisor)):
        raise TypeError

    return z3.SRem(dividend, divisor)
