import pytest
from mock import patch

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.ethereum.call import SymbolicCalldata
from mythril.laser.ethereum.transaction import TransactionStartSignal

from mythril.laser.ethereum.evm_exceptions import WriteProtection


def get_global_state():
    active_account = Account("0x0", code=Disassembly("60606040"))
    environment = Environment(
        active_account, None, SymbolicCalldata("2"), None, None, None, None
    )
    world_state = WorldState()
    world_state.put_account(active_account)
    state = GlobalState(world_state, environment, None, MachineState(gas_limit=8000000))
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=world_state, gas_limit=8000000), None)
    )
    return state


@patch(
    "mythril.laser.ethereum.instructions.get_call_parameters",
    return_value=(
        "0",
        Account(code=Disassembly(code="0x00"), address="0x19"),
        0,
        0,
        0,
        0,
        0,
    ),
)
def test_staticcall(f1):
    # Arrange
    state = get_global_state()
    state.mstate.stack = [10, 10, 10, 10, 10, 10, 10, 10, 0]
    instruction = Instruction("staticcall", dynamic_loader=None)

    # Act and Assert
    with pytest.raises(TransactionStartSignal) as ts:
        instruction.evaluate(state)
    assert ts.value.transaction.static
    assert ts.value.transaction.initial_global_state().environment.static


test_data = (
    "selfdestruct",
    "create",
    "create2",
    "log0",
    "log1",
    "log2",
    "log3",
    "log4",
    "sstore",
)


@pytest.mark.parametrize("input", test_data)
def test_staticness(input):
    # Arrange
    state = get_global_state()
    state.environment.static = True
    state.mstate.stack = []
    instruction = Instruction(input, dynamic_loader=None)

    # Act and Assert
    with pytest.raises(WriteProtection):
        instruction.evaluate(state)


test_data_call = ((0, True), (100, False))


@pytest.mark.parametrize("input, success", test_data_call)
@patch("mythril.laser.ethereum.instructions.get_call_parameters")
def test_staticness_call_concrete(f1, input, success):
    # Arrange
    state = get_global_state()
    state.environment.static = True
    state.mstate.stack = [10] * 100
    code = Disassembly(code="616263")
    f1.return_value = ("0", Account(code=code, address="0x19"), 0, input, 0, 0, 0)
    instruction = Instruction("call", dynamic_loader=None)

    # Act and Assert
    if success:
        with pytest.raises(TransactionStartSignal) as ts:
            instruction.evaluate(state)
        assert ts.value.transaction.static
    else:
        with pytest.raises(WriteProtection):
            instruction.evaluate(state)


@patch("mythril.laser.ethereum.instructions.get_call_parameters")
def test_staticness_call_symbolic(f1):
    # Arrange
    state = get_global_state()
    state.environment.static = True
    state.mstate.stack = [10] * 100
    call_value = symbol_factory.BitVecSym("x", 256)
    code = Disassembly(code="616263")
    f1.return_value = ("0", Account(code=code, address="0x19"), 0, call_value, 0, 0, 0)
    instruction = Instruction("call", dynamic_loader=None)

    # Act and Assert
    with pytest.raises(TransactionStartSignal) as ts:
        instruction.evaluate(state)

    assert ts.value.transaction.static
    assert ts.value.global_state.world_state.constraints[-1] == (call_value == 0)
