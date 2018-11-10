import pytest
from mythril.laser.ethereum.state import Calldata
from z3 import Solver, simplify
from z3.z3types import Z3Exception
from mock import MagicMock

uninitialized_test_data = [
    ([]),  # Empty concrete calldata
    ([1, 4, 5, 3, 4, 72, 230, 53]),  # Concrete calldata
]


@pytest.mark.parametrize("starting_calldata", uninitialized_test_data)
def test_concrete_calldata_uninitialized_index(starting_calldata):
    # Arrange
    calldata = Calldata(0, starting_calldata)
    solver = Solver()

    # Act
    value, constraint1 = calldata[100]
    value2, constraint2 = calldata.get_word_at(200)

    solver.add(constraint1)
    solver.add(constraint2)

    solver.check()
    model = solver.model()

    value = model.eval(value)
    value2 = model.eval(value2)

    # Assert
    assert value == 0
    assert value2 == 0


def test_concrete_calldata_calldatasize():
    # Arrange
    calldata = Calldata(0, [1, 4, 7, 3, 7, 2, 9])
    solver = Solver()

    # Act
    solver.check()
    model = solver.model()

    result = model.eval(calldata.calldatasize)

    # Assert
    assert result == 7


def test_symbolic_calldata_constrain_index():
    # Arrange
    calldata = Calldata(0)
    solver = Solver()

    # Act
    value, calldata_constraints = calldata[100]
    constraint = value == 50

    solver.add([constraint] + calldata_constraints)

    solver.check()
    model = solver.model()

    value = model.eval(value)
    calldatasize = model.eval(calldata.calldatasize)

    # Assert
    assert value == 50
    assert simplify(calldatasize >= 100)


def test_concrete_calldata_constrain_index():
    # Arrange
    calldata = Calldata(0, [1, 4, 7, 3, 7, 2, 9])
    solver = Solver()

    # Act
    value, calldata_constraints = calldata[2]
    constraint = value == 3

    solver.add([constraint] + calldata_constraints)
    result = solver.check()

    # Assert
    assert str(result) == "unsat"


def test_concrete_calldata_constrain_index():
    # Arrange
    calldata = Calldata(0)
    mstate = MagicMock()
    mstate.constraints = []
    solver = Solver()

    # Act
    constraints = []
    value, calldata_constraints = calldata[51]
    constraints.append(value == 1)
    constraints.append(calldata.calldatasize == 50)

    solver.add(constraints + calldata_constraints)

    result = solver.check()

    # Assert
    assert str(result) == "unsat"
