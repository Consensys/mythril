from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.ethereum.state.calldata import ConcreteCalldata
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.smt import symbol_factory

# contract A {
#    uint256 public val = 10;
# }
contract_init_code = "6080604052600a600055348015601457600080fd5b506084806100236000396000f3fe6080604052348015600f57600080fd5b506004361060285760003560e01c80633c6bb43614602d575b600080fd5b60336049565b6040518082815260200191505060405180910390f35b6000548156fea265627a7a72315820d3cfe7a909450a953cbd7e47d8c17477f2609baa5208d043e965efec69d1ed9864736f6c634300050b0032"
contract_runtime_code = "6080604052348015600f57600080fd5b506004361060285760003560e01c80633c6bb43614602d575b600080fd5b60336049565b6040518082815260200191505060405180910390f35b6000548156fea265627a7a72315820d3cfe7a909450a953cbd7e47d8c17477f2609baa5208d043e965efec69d1ed9864736f6c634300050b0032"

last_state = None
created_contract_account = None


def execute_create():
    global last_state
    global created_contract_account
    if not last_state and not created_contract_account:
        code_raw = []
        for i in range(len(contract_init_code) // 2):
            code_raw.append(int(contract_init_code[2 * i : 2 * (i + 1)], 16))
        calldata = ConcreteCalldata(0, code_raw)

        world_state = WorldState()
        account = world_state.create_account(balance=1000000, address=101)
        account.code = Disassembly("60a760006000f000")
        environment = Environment(account, None, calldata, None, None, None)
        og_state = GlobalState(
            world_state, environment, None, MachineState(gas_limit=8000000)
        )
        og_state.transaction_stack.append(
            (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
        )

        laser = LaserEVM()
        states = [og_state]
        last_state = og_state
        for state in states:
            new_states, op_code = laser.execute_state(state)
            last_state = state
            if op_code == "STOP":
                break
            states.extend(new_states)

        created_contract_address = last_state.mstate.stack[-1].value
        created_contract_account = last_state.world_state.accounts[
            created_contract_address
        ]

    return last_state, created_contract_account


def test_create_has_code():
    last_state, created_contract_account = execute_create()
    assert created_contract_account.code.bytecode == contract_runtime_code


def test_create_has_storage():
    last_state, created_contract_account = execute_create()
    storage = created_contract_account.storage
    # From contract, val = 10.
    assert storage[symbol_factory.BitVecVal(0, 256)] == symbol_factory.BitVecVal(
        10, 256
    )
