import pytest
from mythril.laser.ethereum.state.calldata import ConcreteCalldata, SymbolicCalldata
from mythril.laser.smt import Solver, symbol_factory
from z3 import sat, unsat
from z3.z3types import Z3Exception
from mock import MagicMock

uninitialized_test_data = [
    ([]),  # Empty concrete calldata
    ([1, 4, 5, 3, 4, 72, 230, 53]),  # Concrete calldata
]


@pytest.mark.parametrize("starting_calldata", uninitialized_test_data)
def test_concrete_calldata_uninitialized_index(starting_calldata):
    # Arrange
    calldata = ConcreteCalldata(0, starting_calldata)

    # Act
    value = calldata[100]
    value2 = calldata.get_word_at(200)

    # Assert
    assert value == 0
    assert value2 == 0


def test_concrete_calldata_calldatasize():
    # Arrange
    calldata = ConcreteCalldata(0, [1, 4, 7, 3, 7, 2, 9])
    solver = Solver()

    # Act
    solver.check()
    model = solver.model()
    result = model.eval(calldata.calldatasize.raw)

    # Assert
    assert result == 7


def test_concrete_calldata_constrain_index():
    # Arrange
    calldata = ConcreteCalldata(0, [1, 4, 7, 3, 7, 2, 9])
    solver = Solver()

    # Act
    value = calldata[2]
    constraint = value == 3

    solver.add(constraint)
    result = solver.check()

    # Assert
    assert str(result) == "unsat"


def test_symbolic_calldata_constrain_index():
    # Arrange
    calldata = SymbolicCalldata(0)
    solver = Solver()

    # Act
    value = calldata[51]

    constraints = [value == 1, calldata.calldatasize == 50]

    solver.add(*constraints)

    result = solver.check()

    # Assert
    assert str(result) == "unsat"


def test_symbolic_calldata_equal_indices():
    calldata = SymbolicCalldata(0)

    index_a = symbol_factory.BitVecSym("index_a", 256)
    index_b = symbol_factory.BitVecSym("index_b", 256)

    # Act
    a = calldata[index_a]
    b = calldata[index_b]

    s = Solver()
    s.append(index_a == index_b)
    s.append(a != b)

    # Assert
    assert unsat == s.check()
