from mythril.laser.ethereum.evm_exceptions import VmException
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state import Account
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from mythril.analysis.solver import get_model
from datetime import datetime

import binascii
import json
from pathlib import Path
import pytest
from z3 import ExprRef

evm_test_dir = Path(__file__).parent / "VMTests"

test_types = [
    "vmArithmeticTest",
    "vmBitwiseLogicOperation",
    "vmEnvironmentalInfo",
    "vmPushDupSwapTest",
    "vmSha3Test",
    "vmTests",
]


def load_test_data(designations):
    return_data = []
    for designation in designations:
        for file_reference in (evm_test_dir / designation).iterdir():

            with file_reference.open() as file:
                top_level = json.load(file)

                for test_name, data in top_level.items():
                    pre_condition = data["pre"]

                    action = data["exec"]

                    post_condition = data.get("post", {})

                    return_data.append(
                        (test_name, pre_condition, action, post_condition)
                    )

    return return_data


@pytest.mark.parametrize(
    "test_name, pre_condition, action, post_condition", load_test_data(test_types)
)
def test_vmtest(
    test_name: str, pre_condition: dict, action: dict, post_condition: dict
) -> None:
    # Arrange
    if test_name == "gasprice":
        return
    accounts = {}
    for address, details in pre_condition.items():
        account = Account(address)
        account.code = Disassembly(details["code"][2:])
        account.balance = int(details["balance"], 16)
        account.nonce = int(details["nonce"], 16)

        accounts[address] = account

    laser_evm = LaserEVM(accounts)

    # Act
    laser_evm.time = datetime.now()

    # TODO: move this line below and check for VmExceptions when gas has been implemented
    if post_condition == {}:
        return

    execute_message_call(
        laser_evm,
        callee_address=action["address"],
        caller_address=action["caller"],
        origin_address=binascii.a2b_hex(action["origin"][2:]),
        code=action["code"][2:],
        gas=action["gas"],
        data=binascii.a2b_hex(action["data"][2:]),
        gas_price=int(action["gasPrice"], 16),
        value=int(action["value"], 16),
    )

    # Assert

    assert len(laser_evm.open_states) == 1

    world_state = laser_evm.open_states[0]
    model = get_model(next(iter(laser_evm.nodes.values())).states[0].mstate.constraints)

    for address, details in post_condition.items():
        account = world_state[address]

        assert account.nonce == int(details["nonce"], 16)
        assert account.code.bytecode == details["code"][2:]

        for index, value in details["storage"].items():
            expected = int(value, 16)
            actual = account.storage[int(index, 16)]
            if isinstance(actual, ExprRef):
                actual = model.eval(actual)
                actual = 1 if actual == True else 0 if actual == False else actual
            else:
                if type(actual) == bytes:
                    actual = int(binascii.b2a_hex(actual), 16)
                elif type(actual) == str:
                    actual = int(actual, 16)
            assert actual == expected
