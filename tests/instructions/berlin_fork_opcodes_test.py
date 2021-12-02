import pytest

from mythril.laser.ethereum.evm_exceptions import VmException, OutOfGasException
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.smt import symbol_factory, simplify


def get_state():
    world_state = WorldState()
    account = world_state.create_account(balance=10, address=101)
    account.code = Disassembly("0x60045e005c5d")
    environment = Environment(account, None, None, None, None, None, None)
    state = GlobalState(world_state, environment, None, MachineState(gas_limit=8000000))
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )
    return state


BVV = symbol_factory.BitVecVal
BV = symbol_factory.BitVecSym

test_data = (([BVV(5, 256)], [], 2, -1, ()),)


def test_jumpsub_success():
    # Arrange
    state = get_state()
    state.mstate.pc = 2
    state.mstate.stack = [BVV(4, 256)]
    state.mstate.subroutine_stack = []
    instruction = Instruction("jumpsub", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert new_state.mstate.pc == 5
    assert new_state.mstate.stack == []
    assert new_state.mstate.subroutine_stack == [3]


def test_jumpsub_fail():
    # Arrange
    state = get_state()
    state.mstate.pc = 2
    state.mstate.stack = [BVV(5, 256)]
    state.mstate.subroutine_stack = []
    instruction = Instruction("jumpsub", dynamic_loader=None)

    # Act + Assert
    with pytest.raises(VmException):
        instruction.evaluate(state)[0]


def test_beginsub():
    # Arrange
    state = get_state()
    state.mstate.pc = 3
    state.mstate.stack = []
    state.mstate.subroutine_stack = []
    instruction = Instruction("beginsub", dynamic_loader=None)

    # Act + Assert
    with pytest.raises(OutOfGasException):
        instruction.evaluate(state)[0]


def test_returnsub():
    # Arrange
    state = get_state()
    state.mstate.pc = 5
    state.mstate.stack = []
    state.mstate.subroutine_stack = [3]
    instruction = Instruction("returnsub", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert new_state.mstate.pc == 3
