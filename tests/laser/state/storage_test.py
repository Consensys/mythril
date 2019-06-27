import pytest
from mythril.laser.smt import symbol_factory
from mythril.laser.ethereum.state.account import Storage
from mythril.laser.smt import Expression

BVV = symbol_factory.BitVecVal

storage_uninitialized_test_data = [({}, 1), ({1: 5}, 2), ({1: 5, 3: 10}, 2)]


@pytest.mark.parametrize("initial_storage,key", storage_uninitialized_test_data)
def test_concrete_storage_uninitialized_index(initial_storage, key):
    # Arrange
    storage = Storage(concrete=True)
    for k, val in initial_storage.items():
        storage[BVV(k, 256)] = BVV(val, 256)

    # Act
    value = storage[BVV(key, 256)]

    # Assert
    assert value == 0


@pytest.mark.parametrize("initial_storage,key", storage_uninitialized_test_data)
def test_symbolic_storage_uninitialized_index(initial_storage, key):
    # Arrange
    storage = Storage(concrete=False)
    for k, val in initial_storage.items():
        storage[BVV(k, 256)] = BVV(val, 256)

    # Act
    value = storage[BVV(key, 256)]

    # Assert
    assert isinstance(value, Expression)


def test_storage_set_item():
    # Arrange
    storage = Storage()

    # Act
    storage[BVV(1, 256)] = BVV(13, 256)

    # Assert
    assert storage[BVV(1, 256)] == BVV(13, 256)


def test_storage_change_item():
    # Arrange
    storage = Storage()
    storage[BVV(1, 256)] = BVV(12, 256)
    # Act
    storage[BVV(1, 256)] = BVV(14, 256)

    # Assert
    assert storage[BVV(1, 256)] == BVV(14, 256)
