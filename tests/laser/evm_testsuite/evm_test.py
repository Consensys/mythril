from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state import Account
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from datetime import datetime
from z3 import is_true, simplify
from mythril.laser.ethereum.util import get_concrete_int
import json
from pathlib import Path
import pytest

evm_test_dir = Path(__file__).parent / 'VMTests'


def load_test_data(designation):
    return_data = []

    for file_reference in (evm_test_dir / designation).iterdir():
        if file_reference.name.startswith('exp'):
            continue

        with file_reference.open() as file:
            top_level = json.load(file)

            for test_name, data in top_level.items():
                pre_condition = data['pre']

                action = data['exec']

                post_condition = data['post']

                return_data.append((test_name, pre_condition, action, post_condition))

    return return_data


@pytest.mark.parametrize("test_name, pre_condition, action, post_condition", load_test_data('vmArithmeticTest'))
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
        data=(),
        gas_price=int(action['gasPrice'], 16),
        value=int(action['value'], 16)
    )

    # Assert
    assert len(laser_evm.open_states) == 1
    world_state = laser_evm.open_states[0]

    for address, details in post_condition.items():
        account = world_state[address]

        assert account.nonce == int(details['nonce'], 16)
        assert account.code.bytecode == details['code'][2:]

        for index, value in details['storage'].items():
            expected = int(value, 16)
            actual = get_concrete_int(account.storage[int(index, 16)])
            assert actual == expected
