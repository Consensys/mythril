from enum import Enum, auto
from functools import reduce

from pysmt import shortcuts
from pysmt.shortcuts import \
    Symbol, Bool, Int, BV, \
    BVOne, BVZero, BVConcat, BVExtract, BVULT, BVUGT, BVSLT, BVSGT, \
    BVUDiv, BVSDiv, BVURem, BVSRem, \
    Ite, Equals, NotEquals
from pysmt.fnode import FNode
from pysmt.typing import BOOL, BVType, INT
from pysmt.solvers.solver import Solver as SolverType
from pysmt.exceptions import SolverReturnedUnknownResultError


class Types:
    #: Constraints, formulas and items are constraint expressions.
    Expr = FNode


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

    if not (is_expr(expr) and expr.is_constant()):
        raise NotConcreteValueError(expr)
    return expr.constant_value()


def __get_type(op):
    if not is_expr(op):
        return str(type(op))
    return str(op.get_type())


def __try_get_bv(expr) -> Types.Expr:
    return expr if is_bv(expr) else None


def __intbool_to_bv(expr, width: int) -> Types.Expr:
    if isinstance(expr, int):
        return BV(int(expr), width)

    if is_bool(expr):
        return Ite(expr, BVOne(width), BVZero(width))

    if is_int_value(expr):
        return BV(expr.constant_value(), width)

    raise TypeError("{} of type {} is not int or bool".format(
        str(expr), __get_type(expr)))


def __get_bv_pair(op0, op1) -> (Types.Expr, Types.Expr):
    bv0 = __try_get_bv(op0)
    bv1 = __try_get_bv(op1)

    if bv0 is None and bv1 is None:
        raise TypeError(
            "none of {} (type: {}) and {} (type: {}) is bit vector".format(
                str(op0), __get_type(op0), str(op1), __get_type(op1)))

    if bv0 is None:
        bv0 = __intbool_to_bv(op0, bv1.bv_width())
    elif bv1 is None:
        bv1 = __intbool_to_bv(op1, bv0.bv_width())

    return bv0, bv1


def __to_bool(op) -> FNode:
    if isinstance(op, bool):
        return Bool(op)
    if is_bool(op):
        return op
    raise TypeError("{} of type {} cannot be converted to bool formula".format(
        str(op), __get_type(op)))


def __to_int(op) -> FNode:
    if isinstance(op, int):
        return Int(int(op))
    if is_int(op):
        return op
    if is_bool(op):
        return Ite(op, Int(1), Int(0))
    raise TypeError("{} of type {} cannot be converted to int formula".format(
        str(op), __get_type(op)))


def Eq(lhs, rhs) -> Types.Expr:
    """
    Make an equation formula `lhs == rhs`

    :param lhs: the left side of the equation formula
    :param rhs: the right side of the equation formula

    :return: a formula `lhs == rhs`
    """

    try:
        return Equals(__to_bool(lhs), __to_bool(rhs))
    except TypeError:
        pass

    try:
        return Equals(__to_int(lhs), __to_int(rhs))
    except TypeError:
        pass

    return Equals(*__get_bv_pair(lhs, rhs))


def Neq(lhs, rhs) -> Types.Expr:
    """
    Make an inequation formula `lhs <> rhs`

    :param lhs: the left side of the inequation formula
    :param rhs: the right side of the inequation formula

    :return: a formula `lhs <> rhs`
    """

    try:
        return NotEquals(__to_bool(lhs), __to_bool(rhs))
    except TypeError:
        pass

    try:
        return NotEquals(__to_int(lhs), __to_int(rhs))
    except TypeError:
        pass

    return NotEquals(*__get_bv_pair(lhs, rhs))


def SLT(lhs, rhs) -> Types.Expr:
    """
    Make a signed less-than comparison `lhs < rhs`

    :param lhs: the left side of the comparison
    :param rhs: the right side of the comparison

    :return: a signed less-than comparison `lhs < rhs`

    :raise TypeError: if none of them is the bit vector
    """

    return BVSLT(*__get_bv_pair(lhs, rhs))


def SGT(lhs, rhs) -> Types.Expr:
    """
    Make a signed greater-than comparison `lhs > rhs`, or a shortcut formula
    True or False.

    :param lhs: the left side of the comparison
    :param rhs: the right side of the comparison

    :return: a signed greater-than comparison `lhs > rhs`

    :raise TypeError: if none of them is the bit vector
    """

    return BVSGT(*__get_bv_pair(lhs, rhs))


def SDiv(dividend, divisor) -> Types.Expr:
    """
    Make a signed division `dividend / divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: a signed division `dividend / divisor`

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    return BVSDiv(*__get_bv_pair(dividend, divisor))


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
        return expr.simplify()
    except Exception as e:
        reason = str(e)
    raise SimplificationError(reason)


def is_expr(expr) -> bool:
    """
    Check whether `expr` is a constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a formula; False, otherwise.
    """

    return isinstance(expr, Types.Expr)


def is_bv_value(expr) -> bool:
    """
    Check whether `expr` is a concrete bit vector value.

    :param expr: the expression to be checked

    :return: True if `expr` is a concrete bit vector value; False, otherwise.
    """

    return is_expr(expr) and expr.is_bv_constant()


def is_bv(expr) -> bool:
    """
    Check whether `expr` is a bit vector.

    :param expr: the expression to be checked

    :return: True if `expr` is a bit vector; False, otherwise.
    """

    return is_expr(expr) and expr.get_type().is_bv_type()


def is_bool(expr) -> bool:
    """
    Check whether `expr` is a boolean constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a boolen constraint expression; False, otherwise.
    """

    return is_expr(expr) and expr.get_type() == BOOL


def is_true(expr) -> bool:
    """
    Check whether `expr` is a True constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a True constraint expression; False, otherwise.
    """

    return is_expr(expr) and expr.is_true()


def is_false(expr) -> bool:
    """
    Check whether `expr` is a False constraint expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a False constraint expression; False, otherwise.
    """

    return is_expr(expr) and expr.is_false()


def is_int_value(expr) -> bool:
    """
    Check whether `expr` is a constraint integer value.

    :param expr: the expression to be checked

    :return: True if `expr` is a constraint integer value; False, otherwise.
    """

    return is_expr(expr) and expr.is_int_constant()


def is_int(expr) -> bool:
    """
    Check whether `expr` is a constraint integer expression.

    :param expr: the expression to be checked

    :return: True if `expr` is a constraint integer expression; False, otherwise.
    """

    return is_expr(expr) and expr.get_type() == INT


def Not(op) -> Types.Expr:
    """
    Create a Not constraint expression.

    :param op: the operand

    :return: a Not expression

    :raise TypeError: if `op` is neither a Python bool expression nor
                      a constraint bool expression.
    """

    return shortcuts.Not(__to_bool(op))


def BitVec(name: str, width: int) -> Types.Expr:
    """
    Create a bit vector symbol `name` which is `width` bits wide.

    :param name: the symbol name
    :param width: the number of bits

    :return: a bit vector symbol
    """

    return Symbol(name, BVType(width))


def BitVecVal(val: int, width: int) -> Types.Expr:
    """
    Create a bit vector which is `width` bits wide and represent an integer `val`.

    :param val: the value of the bit vector
    :param width: the number of bits of the bit vector

    :return: a bit vector value
    """

    return BV(val, width)


def Concat(*args) -> Types.Expr:
    """
    Concatenate a sequence of bit vectors.

    :param args: the sequence of bit vectors

    :return: the concatenation of the sequence of bit vectors
    """

    return reduce(BVConcat, args)


def Extract(last_bit: int, first_bit: int, bv) -> Types.Expr:
    """
    Create an expression that extract bits from `first_bit` to `last_bit`
    (included) from a bit vector `bv`.

    :param last_bit: the last bit (included) to be extracted
    :param first_bit: the first bit to be extracted
    :param bv: the bit vector

    :return: an expression to extract bits
    """

    return BVExtract(bv, first_bit, last_bit)


def And(*args) -> Types.Expr:
    """
    Create a logical and expression `\\/ *args`.

    :param args: the sub-exprs of the expression

    :return: a logical and expression

    :raise TypeError: if any of `args` is neither a Python bool expression nor
                      a constraint bool expression.
    """

    return shortcuts.And(map(__to_bool, args))


def Or(*args) -> Types.Expr:
    """
    Create a logical or expression `\\/ *args`.

    :param args: the sub-exprs of the expression

    :return: a logical or expression

    :raise TypeError: if any of `args` is neither a Python bool expression nor
                      a constraint bool expression.
    """

    return shortcuts.Or(map(__to_bool, args))


def ULT(lhs, rhs) -> Types.Expr:
    """
    Create an unsigned less-than comparison `lhs < rhs`.

    :param lhs: the left operand
    :param rhs: the right operand

    :return: `lhs < rhs`

    :raise TypeError: if none of `lhs` and `rhs` is the bit vector
    """

    return BVULT(*__get_bv_pair(lhs, rhs))


def UGT(lhs, rhs) -> Types.Expr:
    """
    Create an unsigned greater-than comparison `lhs > rhs`.

    :param lhs: the left operand
    :param rhs: the right operand

    :return: `lhs > rhs`

    :raise TypeError: if none of `lhs` and `rhs` is the bit vector
    """

    return BVUGT(*__get_bv_pair(lhs, rhs))


def If(cond, then_op, else_op) -> Types.Expr:
    """
    Create a if-then-else expression `Ite cond then_op else_op`.

    :param cond: the condition to be checked
    :param then_op: the then operand
    :param else_op: the else operand

    :return: a if-then-else expression
    """

    return Ite(cond, then_op, else_op)


def UDiv(dividend, divisor) -> Types.Expr:
    """
    Create an unsigned division `dividend / divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: an unsigned division

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    return BVUDiv(*__get_bv_pair(dividend, divisor))


def URem(dividend, divisor) -> Types.Expr:
    """
    Create an unsigned reminder `dividend % divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: an unsigned reminder

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    return BVURem(*__get_bv_pair(dividend, divisor))


def SRem(dividend, divisor) -> Types.Expr:
    """
    Create a signed reminder `dividend % divisor`.

    :param dividend: the dividend
    :param divisor: the divisor

    :return: a signed reminder

    :raise TypeError: if none of `dividend` or `divisor` is the bit vector
    """

    return BVSRem(*__get_bv_pair(dividend, divisor))


class Result(Enum):
    """
    Constraint solving results
    """

    sat = auto()
    unsat = auto()
    unknown = auto()


def Solver(timeout=0) -> SolverType:
    """
    Create a constraint solver object.

    :param timeout: time limitation in milliseconds for constraint solving.
                    The default value 0 indicates no time limitation.

    :return: a constraint solver object
    """

    # XXX: solver_options are solver-specific. Passing an unsupported
    #      option to a solver may result in undefined behaviors. When
    #      supporting additional solvers, please take care about the
    #      solver options preparation.
    return shortcuts.Solver(name="z3", solver_options={"timeout": timeout})


def solve(s: SolverType, assumptions=None):
    """
    Check the satisfiability of asserted constraints in the specified solver `s`.
    If the extract constraints `assumptions` are specified, the satisfiability
    check is performed assuming those extra constraints are True.

    :param s: the solver context
    :param assumptions: extract constraints that are assumed True

    :return: `Result.sat` if constraints can be satisfied;
             `Result.unsat` if constraints cannot be satisfied;
             `Result.unknown` if the satisfiability is unknown.
    """

    try:
        result = s.solve(assumptions)
        return Result.sat if result else Result.unsat
    except SolverReturnedUnknownResultError:
        return Result.unknown


def is_always_true(formula, timeout=10000) -> bool:
    """
    Check whether `formula` always holds.

    :param formula: the formula to be checked
    :param timeout: the time limitation milliseconds of constraint solving.
                    The default value is 10 s.

    :return: True if `formula` always holds; False, otherwise (including the
             unknown and timeout cases).
    """

    try:
        return Solver(timeout=timeout).is_unsat(Not(formula))
    except SolverReturnedUnknownResultError:
        return False


def is_always_false(formula, timeout=10000) -> bool:
    """
    Check whether `formula` never holds.

    :param formula: the formula to be checked
    :param timeout: the time limitation milliseconds of constraint solving.
                    The default value is 10 s.

    :return: True if `formula` never holds; False, otherwise (including the
             unknown and timeout cases).
    """

    try:
        return Solver(timeout=timeout).is_unsat(formula)
    except SolverReturnedUnknownResultError:
        return False


def formula_to_string(formula) -> str:
    """
    Get the stringified `formula`.

    If `formula` is not a formula, the default string representation generated
    by `__str__()` will be used.

    Otherwise, a serialized string representation will be used. We do not use
    the default `__str__()`, because it may omit some part of the formula, which
    in turn may cause issues when pattern matching the stringified formula.

    :param formula: the formula

    :return: the stringified `formula`
    """

    return formula.serialize() if is_expr(formula) else str(formula)
