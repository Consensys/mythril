import pytest
from mock import patch
from mock import MagicMock

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction

_world_state = WorldState()
_account = _world_state.create_account(balance=10, address=101)
_account.code = Disassembly("60616240")
_world_state.create_account(balance=10, address=1000)
_environment = Environment(_account, None, None, None, None, None)
ans_state = GlobalState(
    _world_state, _environment, None, MachineState(gas_limit=8000000)
)
ans_state.transaction_stack.append(
    (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
)
ans_state.mstate.memory.extend(32)
ans_state.mstate.memory[2] = 95


@patch(
    "mythril.laser.ethereum.instructions.Instruction._code_copy_helper",
    return_value=[ans_state],
)
@patch(
    "mythril.laser.ethereum.state.world_state.WorldState.accounts_exist_or_load",
    return_value="0x61626364",
)
def test_extcodecopy(f1: MagicMock, f2: MagicMock):
    # Arrange
    new_world_state = WorldState()
    new_account = new_world_state.create_account(balance=10, address=101)
    new_account.code = Disassembly("60616240")
    new_environment = Environment(new_account, None, None, None, None, None)
    state = GlobalState(
        new_world_state, new_environment, None, MachineState(gas_limit=8000000)
    )
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    state.mstate.stack = [2, 2, 2, 10]
    instruction = Instruction("extcodecopy", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]
    new_state.mstate.memory[2] = 95
    # Assert
    print(new_state.mstate.memory._memory)
    assert new_state.mstate.memory[2] == 95


@patch(
    "mythril.laser.ethereum.state.world_state.WorldState.accounts_exist_or_load",
    side_effect=ValueError("foo"),
)
def test_extcodecopy_fail(f1: MagicMock):
    # Arrange
    new_world_state = WorldState()
    new_account = new_world_state.create_account(balance=10, address=101)
    new_account.code = Disassembly("60616240")
    new_environment = Environment(new_account, None, None, None, None, None)
    state = GlobalState(
        new_world_state, new_environment, None, MachineState(gas_limit=8000000)
    )
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    state.mstate.stack = [2, 2, 2, 10]
    instruction = Instruction("extcodecopy", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert new_state.mstate.stack == []
    assert new_state.mstate.memory._memory == state.mstate.memory._memory
