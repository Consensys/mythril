from mythril.laser.smt.independence_solver import _get_expr_variables, DependenceBucket, DependenceMap,\
    IndependenceSolver
from mythril.laser.smt import symbol_factory

import z3


def test_get_expr_variables():
    # Arrange
    x = z3.Bool('x')
    y = z3.BitVec('y', 256)
    z = z3.BitVec('z', 256)
    b = z3.BitVec('b', 256)
    expression = z3.If(x, y, z + b)

    # Act
    variables = list(map(str, _get_expr_variables(expression)))

    # Assert
    assert str(x) in variables
    assert str(y) in variables
    assert str(z) in variables
    assert str(b) in variables


def test_get_expr_variables_num():
    # Arrange
    b = z3.BitVec('b', 256)
    expression = b + z3.BitVecVal(2, 256)

    # Act
    variables = _get_expr_variables(expression)

    # Assert
    assert [b] == variables


def test_create_bucket():
    # Arrange
    x = z3.Bool('x')

    # Act
    bucket = DependenceBucket([x], [x])

    # Assert
    assert [x] == bucket.variables
    assert [x] == bucket.conditions


def test_dependence_map():
    # Arrange
    x = z3.BitVec('x', 256)
    y = z3.BitVec('y', 256)
    z = z3.BitVec('z', 256)
    a = z3.BitVec('a', 256)
    b = z3.BitVec('b', 256)

    conditions = [
        x > y,
        y == z,
        a == b
    ]

    dependence_map = DependenceMap()

    # Act
    for condition in conditions:
        dependence_map.add_condition(condition)

    # Assert
    assert 2 == len(dependence_map.buckets)

    assert x in dependence_map.buckets[0].variables
    assert y in dependence_map.buckets[0].variables
    assert z in dependence_map.buckets[0].variables

    assert conditions[0] in dependence_map.buckets[0].conditions
    assert conditions[1] in dependence_map.buckets[0].conditions

    assert a in dependence_map.buckets[1].variables
    assert b in dependence_map.buckets[1].variables

    assert conditions[2] in dependence_map.buckets[1].conditions


def test_Independence_solver_unsat():
    # Arrange
    x = symbol_factory.BitVecSym('x', 256)
    y = symbol_factory.BitVecSym('y', 256)
    z = symbol_factory.BitVecSym('z', 256)
    a = symbol_factory.BitVecSym('a', 256)
    b = symbol_factory.BitVecSym('b', 256)

    conditions = [
        x > y,
        y == z,
        y != z,
        a == b
    ]

    solver = IndependenceSolver()

    # Act
    solver.add(conditions)
    result = solver.check()

    # Assert
    assert z3.unsat == result


def test_independence_solver_unsat_in_second_bucket():
    # Arrange
    x = symbol_factory.BitVecSym('x', 256)
    y = symbol_factory.BitVecSym('y', 256)
    z = symbol_factory.BitVecSym('z', 256)
    a = symbol_factory.BitVecSym('a', 256)
    b = symbol_factory.BitVecSym('b', 256)

    conditions = [
        x > y,
        y == z,
        a == b,
        a != b
    ]

    solver = IndependenceSolver()

    # Act
    solver.add(conditions)
    result = solver.check()

    # Assert
    assert z3.unsat == result


def test_independence_solver_sat():
    # Arrange
    x = symbol_factory.BitVecSym('x', 256)
    y = symbol_factory.BitVecSym('y', 256)
    z = symbol_factory.BitVecSym('z', 256)
    a = symbol_factory.BitVecSym('a', 256)
    b = symbol_factory.BitVecSym('b', 256)

    conditions = [
        x > y,
        y == z,
        a == b,
    ]

    solver = IndependenceSolver()

    # Act
    solver.add(conditions)
    result = solver.check()

    # Assert
    assert z3.sat == result
