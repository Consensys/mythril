from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.smt import symbol_factory


def test_basefee():
    # Arrange
    world_state = WorldState()
    account = world_state.create_account(balance=10, address=101)
    account.code = Disassembly("60606040")
    environment = Environment(
        account,
        None,
        None,
        None,
        None,
        None,
        basefee=symbol_factory.BitVecSym("gasfee", 256),
    )
    og_state = GlobalState(
        world_state, environment, None, MachineState(gas_limit=8000000)
    )
    og_state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    og_state.mstate.stack = []
    instruction = Instruction("basefee", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(og_state)[0]

    # Assert
    assert new_state.mstate.stack == [symbol_factory.BitVecSym("gasfee", 256)]
