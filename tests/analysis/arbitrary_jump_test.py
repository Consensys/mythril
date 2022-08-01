import pytest
from mock import patch

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.smt import symbol_factory, BitVec
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.constraints import Constraints
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.ethereum.call import SymbolicCalldata
from mythril.laser.ethereum.transaction import TransactionStartSignal
from mythril.analysis.module.modules.arbitrary_jump import (
    is_unique_jumpdest,
    ArbitraryJump,
)
from mythril.laser.ethereum.time_handler import time_handler


def get_global_state(constraints):
    """Constructs an arbitrary global state

    Args:
        constraints (List[BitVec]): Constraints list for the global state

    Returns:
        [GlobalState]: An arbitrary global state
    """
    active_account = Account("0x0", code=Disassembly("60606040"))
    environment = Environment(
        active_account, None, SymbolicCalldata("2"), None, None, None, None
    )
    world_state = WorldState()
    world_state.put_account(active_account)
    state = GlobalState(world_state, environment, None, MachineState(gas_limit=8000000))
    state.world_state.transaction_sequence = [
        MessageCallTransaction(
            world_state=world_state,
            gas_limit=8000000,
            init_call_data=True,
            call_value=symbol_factory.BitVecSym("call_value", 256),
            caller=ACTORS.attacker,
            callee_account=active_account,
        )
    ]
    state.transaction_stack.append(
        (
            MessageCallTransaction(
                world_state=world_state, gas_limit=8000000, init_call_data=True
            ),
            None,
        )
    )
    state.mstate.stack = [symbol_factory.BitVecSym("jump_dest", 256)]

    state.world_state.constraints = Constraints(constraints)
    return state


test_data = (
    (
        get_global_state([symbol_factory.BitVecSym("jump_dest", 256) == 222]),
        True,
    ),
    (
        get_global_state([symbol_factory.BitVecSym("jump_dest", 256) > 222]),
        False,
    ),
)


@pytest.mark.parametrize("global_state, unique", test_data)
def test_unique_jumpdest(global_state, unique):
    time_handler.start_execution(10)
    assert is_unique_jumpdest(global_state.mstate.stack[-1], global_state) == unique


test_data = (
    (
        get_global_state([symbol_factory.BitVecSym("jump_dest", 256) == 222]),
        False,
    ),
    (
        get_global_state([symbol_factory.BitVecSym("jump_dest", 256) > 222]),
        True,
    ),
)


@pytest.mark.parametrize("global_state, has_issue", test_data)
def test_module(global_state, has_issue):
    time_handler.start_execution(10)
    module = ArbitraryJump()
    assert (len(module._analyze_state(global_state)) > 0) == has_issue
