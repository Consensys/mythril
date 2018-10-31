from mythril.laser.ethereum.transaction.symbolic import (
    execute_message_call,
    execute_contract_creation,
)
from mythril.laser.ethereum.transaction import (
    MessageCallTransaction,
    ContractCreationTransaction,
)
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state import WorldState, Account
import unittest.mock as mock
from unittest.mock import MagicMock
from mythril.laser.ethereum.transaction.symbolic import (
    _setup_global_state_for_execution,
)


def _is_message_call(_, transaction):
    assert isinstance(transaction, MessageCallTransaction)


def _is_contract_creation(_, transaction):
    assert isinstance(transaction, ContractCreationTransaction)


@mock.patch(
    "mythril.laser.ethereum.transaction.symbolic._setup_global_state_for_execution"
)
def test_execute_message_call(mocked_setup: MagicMock):
    # Arrange
    laser_evm = LaserEVM({})

    world_state = WorldState()
    world_state.accounts["address"] = Account("address")

    laser_evm.open_states = [world_state]
    laser_evm.exec = MagicMock()

    mocked_setup.side_effect = _is_message_call

    # Act
    execute_message_call(laser_evm, "address")

    # Assert
    # laser_evm.exec.assert_called_once()
    assert laser_evm.exec.call_count == 1
    # mocked_setup.assert_called_once()
    assert mocked_setup.call_count == 1

    assert len(laser_evm.open_states) == 0


@mock.patch(
    "mythril.laser.ethereum.transaction.symbolic._setup_global_state_for_execution"
)
def test_execute_contract_creation(mocked_setup: MagicMock):
    # Arrange
    laser_evm = LaserEVM({})

    laser_evm.open_states = [WorldState(), WorldState()]
    laser_evm.exec = MagicMock()
    mocked_setup.side_effect = _is_contract_creation

    # Act
    execute_contract_creation(laser_evm, "606000")

    # Assert
    # mocked_setup.assert_called()
    assert mocked_setup.call_count >= 1
    # laser_evm.exec.assert_called_once()
    assert laser_evm.exec.call_count == 1
    assert len(laser_evm.open_states) == 0


def test_calldata_constraints_in_transaction():
    # Arrange
    laser_evm = LaserEVM({})
    world_state = WorldState()

    correct_constraints = [MagicMock(), MagicMock(), MagicMock()]

    transaction = MessageCallTransaction(
        world_state, Account("ca11ee"), Account("ca114")
    )
    transaction.call_data = MagicMock()
    transaction.call_data.constraints = correct_constraints

    # Act
    _setup_global_state_for_execution(laser_evm, transaction)

    # Assert
    state = laser_evm.work_list[0]
    for constraint in correct_constraints:
        assert constraint in state.environment.calldata.constraints
