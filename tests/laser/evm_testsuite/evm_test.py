from mythril.laser.ethereum.exceptions import VmException
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state import Account
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from datetime import datetime
from mythril.laser.ethereum.util import get_concrete_int
import binascii
import json
from pathlib import Path
import pytest

evm_test_dir = Path(__file__).parent / 'VMTests'

test_types = ['vmArithmeticTest', 'vmBitwiseLogicOperation', 'vmPushDupSwapTest']


def load_test_data(designations):
    return_data = []
    for designation in designations:
        for file_reference in (evm_test_dir / designation).iterdir():

            with file_reference.open() as file:
                top_level = json.load(file)

                for test_name, data in top_level.items():
                    pre_condition = data['pre']

                    action = data['exec']

                    post_condition = data.get('post', {})

                    return_data.append((test_name, pre_condition, action, post_condition))

    return return_data


@pytest.mark.parametrize("test_name, pre_condition, action, post_condition", load_test_data(test_types))
def test_vmtest(test_name: str, pre_condition: dict, action: dict, post_condition: dict) -> None:
    # Arrange

    accounts = {}
    for address, details in pre_condition.items():
        account = Account(address)
        account.code = Disassembly(details['code'][2:])
        account.balance = int(details['balance'], 16)
        account.nonce = int(details['nonce'], 16)

        accounts[address] = account

    laser_evm = LaserEVM(accounts)

    # Act
    laser_evm.time = datetime.now()
    execute_message_call(
        laser_evm,
        callee_address=action['address'],
        caller_address=action['caller'],
        origin_address=action['origin'],
        code=action['code'][2:],
        gas=action['gas'],
        data=binascii.a2b_hex(action['data'][2:]),
        gas_price=int(action['gasPrice'], 16),
        value=int(action['value'], 16)
    )

    # Assert

    if 'Suicide' not in test_name and post_condition != {}:
        assert len(laser_evm.open_states) == 1
    else:
        if 'Suicide' in test_name:
            assert 0 == len(laser_evm.open_states)
        return

    world_state = laser_evm.open_states[0]

    for address, details in post_condition.items():
        account = world_state[address]

        assert account.nonce == int(details['nonce'], 16)
        assert account.code.bytecode == details['code'][2:]

        for index, value in details['storage'].items():
            expected = int(value, 16)
            actual = get_concrete_int(account.storage[int(index, 16)])
            assert actual == expected
