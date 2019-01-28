from mythril.laser.smt import Solver, symbol_factory
import z3


def test_decls():
    # Arrange
    solver = Solver()
    x = symbol_factory.BitVecSym("x", 256)
    expression = x == symbol_factory.BitVecVal(2, 256)

    # Act
    solver.add(expression)
    result = solver.check()
    model = solver.model()

    decls = model.decls()

    # Assert
    assert z3.sat == result
    assert x.raw.decl() in decls


def test_get_item():
    # Arrange
    solver = Solver()
    x = symbol_factory.BitVecSym("x", 256)
    expression = x == symbol_factory.BitVecVal(2, 256)

    # Act
    solver.add(expression)
    result = solver.check()
    model = solver.model()

    x_concrete = model[x.raw.decl()]

    # Assert
    assert z3.sat == result
    assert 2 == x_concrete


def test_as_long():
    # Arrange
    solver = Solver()
    x = symbol_factory.BitVecSym("x", 256)
    expression = x == symbol_factory.BitVecVal(2, 256)

    # Act
    solver.add(expression)
    result = solver.check()
    model = solver.model()

    x_concrete = model.eval(x.raw).as_long()

    # Assert
    assert z3.sat == result
    assert 2 == x_concrete
