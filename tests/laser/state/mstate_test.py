import pytest
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.evm_exceptions import StackUnderflowException

stack_pop_too_many_test_data = [(0, 1), (0, 2), (5, 1), (5, 10)]


@pytest.mark.parametrize("initial_size,overflow", stack_pop_too_many_test_data)
def test_stack_pop_too_many(initial_size, overflow):
    # Arrange
    machine_state = MachineState(0)
    machine_state.stack = [42] * initial_size

    # Act + Assert
    with pytest.raises(StackUnderflowException):
        machine_state.pop(initial_size + overflow)


stack_pop_test_data = [
    ([1, 2, 3], 2, [3, 2]),
    ([1, 3, 4, 7, 7, 1, 2], 5, [2, 1, 7, 7, 4]),
]


@pytest.mark.parametrize("initial_stack,amount,expected", stack_pop_test_data)
def test_stack_multiple_pop(initial_stack, amount, expected):
    # Arrange
    machine_state = MachineState(0)
    machine_state.stack = initial_stack[:]

    # Act
    results = machine_state.pop(amount)

    # Assert
    assert results == initial_stack[-amount:][::-1]
    assert results == expected
    assert len(machine_state.stack) == len(initial_stack) - amount


def test_stack_multiple_pop_():
    # Arrange
    machine_state = MachineState(0)
    machine_state.stack = [1, 2, 3]

    # Act
    a, b = machine_state.pop(2)

    # Assert
    assert a == 3
    assert b == 2


def test_stack_single_pop():
    # Arrange
    machine_state = MachineState(0)
    machine_state.stack = [1, 2, 3]

    # Act
    result = machine_state.pop()

    # Assert
    assert isinstance(result, int)
