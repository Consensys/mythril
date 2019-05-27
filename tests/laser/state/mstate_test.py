import pytest
from ethereum import utils
from mythril.laser.smt import simplify, symbol_factory

from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.evm_exceptions import StackUnderflowException
from mythril.laser.ethereum.state.memory import Memory

memory_extension_test_data = [(0, 0, 10), (0, 30, 10), (100, 22, 8)]


@pytest.mark.parametrize(
    "initial_size,start,extension_size", memory_extension_test_data
)
def test_memory_extension(initial_size, start, extension_size):
    # Arrange
    machine_state = MachineState(gas_limit=8000000)
    machine_state.memory = Memory()
    machine_state.memory.extend(initial_size)

    # Act
    machine_state.mem_extend(start, extension_size)

    # Assert
    assert machine_state.memory_size == len(machine_state.memory)
    assert machine_state.memory_size == max(
        initial_size, (utils.ceil32(start + extension_size) // 32) * 32
    )


stack_pop_too_many_test_data = [(0, 1), (0, 2), (5, 1), (5, 10)]


@pytest.mark.parametrize("initial_size,overflow", stack_pop_too_many_test_data)
def test_stack_pop_too_many(initial_size, overflow):
    # Arrange
    machine_state = MachineState(8000000)
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
    machine_state = MachineState(8000000)
    machine_state.stack = initial_stack[:]

    # Act
    results = machine_state.pop(amount)

    # Assert
    assert results == initial_stack[-amount:][::-1]
    assert results == expected
    assert len(machine_state.stack) == len(initial_stack) - amount


def test_stack_multiple_pop_():
    # Arrange
    machine_state = MachineState(8000000)
    machine_state.stack = [1, 2, 3]

    # Act
    a, b = machine_state.pop(2)

    # Assert
    assert a == 3
    assert b == 2


def test_stack_single_pop():
    # Arrange
    machine_state = MachineState(8000000)
    machine_state.stack = [1, 2, 3]

    # Act
    result = machine_state.pop()

    # Assert
    assert isinstance(result, int)


def test_memory_zeroed():
    # Arrange
    mem = Memory()
    mem.extend(2000 + 32)

    # Act
    mem[11] = 10
    mem.write_word_at(2000, 0x12345)

    # Assert
    assert mem[10] == 0
    assert mem[100] == 0
    assert mem.get_word_at(1000) == 0


def test_memory_write():
    # Arrange
    mem = Memory()
    mem.extend(200 + 32)

    a = symbol_factory.BitVecSym("a", 256)
    b = symbol_factory.BitVecSym("b", 8)

    # Act
    mem[11] = 10
    mem[12] = b
    mem.write_word_at(200, 0x12345)
    mem.write_word_at(100, a)

    # Assert
    assert mem[0] == 0
    assert mem[11] == 10
    assert mem[200 + 31] == 0x45
    assert mem.get_word_at(200) == 0x12345
    assert simplify(a == mem.get_word_at(100))
    assert simplify(b == mem[12])
