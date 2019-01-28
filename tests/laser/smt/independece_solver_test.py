from mythril.laser.smt.independence_solver import _get_expr_variables
import z3


def test_get_expr_variables():
    # Arrange
    x = z3.Bool('x')
    y = z3.Int('y')
    z = z3.Int('z')
    b = z3.Int('b')
    expression = z3.If(x, y, z + b)

    # Act
    variables = _get_expr_variables(expression)

    # Assert
    assert x in variables
    assert y in variables
    assert z in variables
    assert b in variables


def test_get_expr_variables_num():
    # Arrange
    b = z3.BitVec('b', 256)
    expression = b + z3.BitVecVal(2, 256)

    # Act
    variables = _get_expr_variables(expression)

    # Assert
    assert [b] == variables
