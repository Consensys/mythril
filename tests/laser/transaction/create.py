import mythril.laser.ethereum.transaction as transaction
import mythril.laser.ethereum.svm as svm
from datetime import datetime
from mythril.ether.soliditycontract import SolidityContract
import tests


def test_create():
    contract = SolidityContract(str(tests.TESTDATA_INPUTS_CONTRACTS / 'calls.sol'))

    laser_evm = svm.LaserEVM({})

    laser_evm.time = datetime.now()
    laser_evm.execute_contract_creation(contract.creation_code)

    print('after')
