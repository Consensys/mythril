from mythril.laser.smt import symbol_factory
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction


def test_extcodecopy():
    # Arrange
    new_world_state = WorldState()
    new_account = new_world_state.create_account(balance=10, address=101)
    new_account.code = Disassembly("60616240")
    ext_account = new_world_state.create_account(balance=1000, address=121)
    ext_account.code = Disassembly("6040404040")

    new_environment = Environment(new_account, None, None, None, None, None, None)
    state = GlobalState(
        new_world_state, new_environment, None, MachineState(gas_limit=8000000)
    )
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    state.mstate.stack = [3, 0, 0, 121]
    instruction = Instruction("extcodecopy", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]
    # Assert
    assert new_state.mstate.memory[0:3] == [96, 64, 64]


def test_extcodecopy_fail():
    # Arrange
    new_world_state = WorldState()
    new_account = new_world_state.create_account(balance=10, address=101)
    new_account.code = Disassembly("60616240")
    new_environment = Environment(new_account, None, None, None, None, None, None)
    state = GlobalState(
        new_world_state, new_environment, None, MachineState(gas_limit=8000000)
    )
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    state.mstate.stack = [2, 2, 2, symbol_factory.BitVecSym("FAIL", 256)]
    instruction = Instruction("extcodecopy", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert new_state.mstate.stack == []
    assert new_state.mstate.memory._memory == state.mstate.memory._memory
