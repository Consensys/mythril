from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction

from mythril.support.support_utils import get_code_hash

from mythril.laser.smt import symbol_factory


def test_extcodehash_concrete():
    # Arrange
    world_state = WorldState()
    account = world_state.create_account(balance=10, address=101)
    account.code = Disassembly("60606040")
    world_state.create_account(balance=10, address=1000)
    environment = Environment(account, None, None, None, None, None)
    og_state = GlobalState(
        world_state, environment, None, MachineState(gas_limit=8000000)
    )
    og_state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    instruction = Instruction("extcodehash", dynamic_loader=None)

    # If account does not exist, return 0
    og_state.mstate.stack = [symbol_factory.BitVecVal(1, 256)]
    new_state = instruction.evaluate(og_state)[0]
    assert new_state.mstate.stack[-1] == 0

    # If account code does not exist, return hash of empty set.
    og_state.mstate.stack = [symbol_factory.BitVecVal(1000, 256)]
    new_state = instruction.evaluate(og_state)[0]
    assert (
        new_state.mstate.stack[-1]
        == "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    )

    # If account code exists, return hash of the code.
    og_state.mstate.stack = [symbol_factory.BitVecVal(101, 256)]
    new_state = instruction.evaluate(og_state)[0]
    assert new_state.mstate.stack[-1] == get_code_hash("60606040")
