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

evm_test_dir = Path(__file__).parent / "VMTests"

test_types = [
    "vmArithmeticTest",
    "vmBitwiseLogicOperation",
    "vmPushDupSwapTest",
    "vmTests",
    # "vmSha3Test"
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
                    gas_before = int(action["gas"], 16)
                    gas_after = data.get("gas")
                    gas_used = gas_before - int(gas_after, 16) if gas_after is not None else None

                    post_condition = data.get("post", {})
                    environment = data.get("env")

                    return_data.append(
                        (test_name, environment, pre_condition, action, gas_used, post_condition)
                    )

    return return_data


@pytest.mark.parametrize(
    "test_name, environment, pre_condition, action, gas_used, post_condition", load_test_data(test_types)
)
def test_vmtest(
    test_name: str, environment: dict, pre_condition: dict, action: dict, gas_used:int, post_condition: dict
) -> None:
    # Arrange

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

    if post_condition == {}:
        return

    final_states = execute_message_call(
        laser_evm,
        callee_address=action["address"],
        caller_address=action["caller"],
        origin_address=action["origin"],
        code=action["code"][2:],
        gas_limit=int(environment["currentGasLimit"], 16),
        data=binascii.a2b_hex(action["data"][2:]),
        gas_price=int(action["gasPrice"], 16),
        value=int(action["value"], 16),
        track_gas=True
    )

    # Assert
    gas_min_max = [(s.mstate.min_gas_used, s.mstate.max_gas_used) for s in final_states]
    assert all(map(lambda g: g[0] <= g[1], gas_min_max))
    if gas_used:
        gas_ranges = map(lambda g: g[0] <= gas_used <= g[1], gas_min_max)
        assert any(gas_ranges)

    assert len(laser_evm.open_states) == 1

    world_state = laser_evm.open_states[0]
    model = get_model(next(iter(laser_evm.nodes.values())).states[0].mstate.constraints)

    for address, details in post_condition.items():
        account = world_state[address]

        assert account.nonce == int(details["nonce"], 16)
        assert account.code.bytecode == details["code"][2:]

        for index, value in details["storage"].items():
            expected = int(value, 16)
            if type(account.storage[int(index, 16)]) != int:
                actual = model.eval(account.storage[int(index, 16)])
                actual = 1 if actual == True else 0 if actual == False else actual
            else:
                actual = account.storage[int(index, 16)]
            assert actual == expected
