import pytest
from mythril.laser.ethereum.state.account import Storage
from mythril.laser.smt import Expression
storage_uninitialized_test_data = [({}, 1), ({1: 5}, 2), ({1: 5, 3: 10}, 2)]


@pytest.mark.parametrize("initial_storage,key", storage_uninitialized_test_data)
def test_concrete_storage_uninitialized_index(initial_storage, key):
    # Arrange
    storage = Storage(concrete=True)
    storage._storage = initial_storage

    # Act
    value = storage[key]

    # Assert
    assert value == 0


@pytest.mark.parametrize("initial_storage,key", storage_uninitialized_test_data)
def test_symbolic_storage_uninitialized_index(initial_storage, key):
    # Arrange
    storage = Storage(concrete=False)
    storage._storage = initial_storage

    # Act
    value = storage[key]

    # Assert
    assert isinstance(value, Expression)


def test_storage_set_item():
    # Arrange
    storage = Storage()

    # Act
    storage[1] = 13

    # Assert
    assert storage[1] == 13


def test_storage_change_item():
    # Arrange
    storage = Storage()
    storage._storage = {1: 12}
    # Act
    storage[1] = 14

    # Assert
    assert storage[1] == 14
