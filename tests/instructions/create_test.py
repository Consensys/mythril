from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction

from mythril.laser.ethereum.svm import LaserEVM

from mythril.laser.smt import symbol_factory


def test_create():
    creating_contract_runtime_code = "608060405260043610601c5760003560e01c8063efc81a8c146021575b600080fd5b60276029565b005b60006040516035906056565b604051809103906000f0801580156050573d6000803e3d6000fd5b50905050565b605b806100638339019056fe6080604052348015600f57600080fd5b50603e80601d6000396000f3fe6080604052600080fdfea265627a7a72315820f4040cbd444dcd2f49f1daf46a116eb32396f1cc84a9e79e3836d4bfe84d6bca64736f6c634300050b0032a265627a7a72315820e2350a73a28ed02b4dac678f2b77a330dc512c3cce8ca53fa1c30869f443553d64736f6c634300050b0032"
    created_contract_init_code = "6080604052348015600f57600080fd5b50603e80601d6000396000f3fe6080604052600080fdfea265627a7a72315820f4040cbd444dcd2f49f1daf46a116eb32396f1cc84a9e79e3836d4bfe84d6bca64736f6c634300050b0032"
    created_contract_runtime_code = "6080604052600080fdfea265627a7a72315820f4040cbd444dcd2f49f1daf46a116eb32396f1cc84a9e79e3836d4bfe84d6bca64736f6c634300050b0032"
    world_state = WorldState()
    account = world_state.create_account(balance=1000, address=101)
    account.code = Disassembly(creating_contract_runtime_code)
    environment = Environment(account, None, None, None, None, None)
    og_state = GlobalState(
        world_state, environment, None, MachineState(gas_limit=8000000)
    )
    og_state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )

    laser_evm = LaserEVM()

    new_states, op_code = laser_evm.execute_state(og_state)
    # checks

    # TODO: come up with sequence, then grab an address from stack and check that its code is created.
