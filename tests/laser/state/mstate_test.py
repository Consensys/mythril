import pytest
from mythril.laser.ethereum.state import MachineState

test_data = [
    (0, 0, 10),
    (0, 30, 10),
    (100, 22, 8)
]


@pytest.mark.parametrize("initial_size,start,extension_size", test_data)
def test_memory_extension(initial_size, start, extension_size):
    # Arrange
    machine_state = MachineState(0)
    machine_state.memory = [0] * initial_size

    # Act
    machine_state.mem_extend(start, extension_size)

    # Assert
    assert machine_state.memory_size == len(machine_state.memory)
    assert machine_state.memory_size == max(initial_size, start + extension_size)
