import pytest

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import (
    MessageCallTransaction,
    TransactionStartSignal,
)
from mythril.laser.ethereum.state.calldata import ConcreteCalldata


last_state = None
created_contract_account = None


def test_create():
    world_state = WorldState()
    account = world_state.create_account(balance=10, address=101)
    account.code = Disassembly("60606060")
    environment = Environment(account, None, None, None, None, None, None)
    og_state = GlobalState(
        world_state, environment, None, MachineState(gas_limit=8000000)
    )
    code_raw = []
    code = "606060606060"
    for i in range(len(code) // 2):
        code_raw.append(int(code[2 * i : 2 * (i + 1)], 16))
    calldata = ConcreteCalldata("1", code_raw)
    environment.calldata = calldata
    og_state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )
    value = 3
    og_state.mstate.stack = [6, 0, value]
    instruction = Instruction("create", dynamic_loader=None)
    og_state.mstate.memory.extend(100)
    og_state.mstate.memory[0:6] = [96] * 6

    # Act + Assert
    with pytest.raises(TransactionStartSignal) as t:
        _ = instruction.evaluate(og_state)[0]

    assert t.value.transaction.call_value == value
    assert t.value.transaction.code.bytecode == code
    assert (
        t.value.transaction.callee_account.address
        == world_state._generate_new_address(account.address.value)
    )
