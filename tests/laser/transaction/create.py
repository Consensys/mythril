import mythril.laser.ethereum.transaction as transaction
import mythril.laser.ethereum.svm as svm
from mythril.disassembler.disassembly import Disassembly
from datetime import datetime
from mythril.ether.soliditycontract import SolidityContract
import tests


def test_create():
    contract = SolidityContract(str(tests.TESTDATA_INPUTS_CONTRACTS / 'calls.sol'))

    laser_evm = svm.LaserEVM({})

    laser_evm.time = datetime.now()
    laser_evm.execute_contract_creation(contract.creation_code)

    resulting_final_state = laser_evm.open_states[0]

    for address, created_account in resulting_final_state.world_state.accounts.items():
        created_account_code = created_account.code
        actual_code = Disassembly(contract.code)

        for i in range(len(created_account_code.instruction_list)):
            found_instruction = created_account_code.instruction_list[i]
            actual_instruction = actual_code.instruction_list[i]

            assert found_instruction['opcode'] == actual_instruction['opcode']
