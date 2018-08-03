from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state import MachineState, GlobalState, Environment, Account
from mythril.laser.ethereum.instructions import Instruction


def test_codecopy_concrete():
    # Arrange
    active_account = Account("0x0", code= Disassembly("60606040"))
    environment = Environment(active_account, None, None, None, None, None)
    og_state = GlobalState(None, environment, None, MachineState(gas=10000000))

    og_state.mstate.stack = [2, 2, 2]
    instruction = Instruction("codecopy", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(og_state)[0]

    # Assert
    assert new_state.mstate.memory[2] == 96
    assert new_state.mstate.memory[3] == 64
