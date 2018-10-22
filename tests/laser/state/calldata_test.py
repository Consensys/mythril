import pytest
from mythril.laser.ethereum.state import Calldata
from z3 import Solver, simplify
from z3.z3types import Z3Exception



uninitialized_test_data = [
    (None), # Symbolic calldata
    ([]), # Empty concrete calldata
    ([1,4,5,3,4,72,230,53]) # Concrete calldata
]
@pytest.mark.parametrize("starting_calldata", uninitialized_test_data)
def test_calldata_uninitialized_index(starting_calldata):
    # Arrange
    calldata = Calldata(0, starting_calldata)
    solver = Solver()

    # Act
    value = calldata[100]

    solver.add(calldata.constraints)
    solver.check()
    model = solver.model()

    value = model.eval(value)

    # Assert
    assert value == 0

def test_concrete_calldata_calldatasize():
    # Arrange
    calldata = Calldata(0, [1,4,7,3,7,2,9])
    solver = Solver()

    # Act
    solver.add(calldata.constraints)
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
    constraint = calldata[100] == 50

    value = calldata[100]

    solver.add(calldata.constraints + [constraint])
    solver.check()
    model = solver.model()

    value = model.eval(value)
    calldatasize = model.eval(calldata.calldatasize)

    # Assert
    assert value == 50
    assert simplify(calldatasize >= 100)

def test_concrete_calldata_constrain_index():
    # Arrange
    calldata = Calldata(0, [1,4,7,3,7,2,9])
    solver = Solver()

    # Act
    constraint = calldata[2] == 3

    solver.add(calldata.constraints + [constraint])
    result = solver.check()

    # Assert
    assert str(result) == 'unsat'
