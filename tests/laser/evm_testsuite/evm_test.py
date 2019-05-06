from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.analysis.solver import get_model
from datetime import datetime

import binascii
import json
import os
from pathlib import Path
import pytest
from z3 import ExprRef, simplify

evm_test_dir = Path(__file__).parent / "VMTests"

test_types = [
    "vmArithmeticTest",
    "vmBitwiseLogicOperation",
    "vmEnvironmentalInfo",
    "vmPushDupSwapTest",
    "vmTests",
    "vmSha3Test",
]


def load_test_data(designations):
    """

    :param designations:
    :return:
    """
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
                    gas_used = (
                        gas_before - int(gas_after, 16)
                        if gas_after is not None
                        else None
                    )

                    post_condition = data.get("post", {})
                    environment = data.get("env")

                    return_data.append(
                        (
                            test_name,
                            environment,
                            pre_condition,
                            action,
                            gas_used,
                            post_condition,
                        )
                    )

    return return_data


@pytest.mark.parametrize(
    "test_name, environment, pre_condition, action, gas_used, post_condition",
    load_test_data(test_types),
)
def test_vmtest(
    test_name: str,
    environment: dict,
    pre_condition: dict,
    action: dict,
    gas_used: int,
    post_condition: dict,
) -> None:
    # Arrange
    if test_name == "gasprice":
        return

    world_state = WorldState()

    for address, details in pre_condition.items():
        account = Account(address)
        account.code = Disassembly(details["code"][2:])
        account.nonce = int(details["nonce"], 16)
        world_state.put_account(account)
        account.set_balance(int(details["balance"], 16))

    laser_evm = LaserEVM()
    laser_evm.open_states = [world_state]

    # Act
    laser_evm.time = datetime.now()


    final_states = execute_message_call(
        laser_evm,
        callee_address=symbol_factory.BitVecVal(int(action["address"], 16), 256),
        caller_address=symbol_factory.BitVecVal(int(action["caller"], 16), 256),
        origin_address=symbol_factory.BitVecVal(int(action["origin"], 16), 256),
        code=action["code"][2:],
        gas_limit=int(action["gas"], 16),
        data=binascii.a2b_hex(action["data"][2:]),
        gas_price=int(action["gasPrice"], 16),
        value=int(action["value"], 16),
        track_gas=True,
    )

    # Assert
    if gas_used is not None and gas_used < int(environment["currentGasLimit"], 16):
        # avoid gas usage larger than block gas limit
        # this currently exceeds our estimations
        gas_min_max = [
            (s.mstate.min_gas_used, s.mstate.max_gas_used) for s in final_states
        ]
        gas_ranges = [g[0] <= gas_used for g in gas_min_max]
        assert all(map(lambda g: g[0] <= g[1], gas_min_max))
        assert any(gas_ranges)

    if any((v in test_name for v in ["error", "oog"])) and post_condition == {}:
        # no more work to do if error happens or out of gas
        assert len(laser_evm.open_states) == 0
    else:
        assert len(laser_evm.open_states) == 1
        world_state = laser_evm.open_states[0]
        model = get_model(
            next(iter(laser_evm.nodes.values())).states[0].mstate.constraints,
            enforce_execution_time=False,
        )

        for address, details in post_condition.items():
            account = world_state[symbol_factory.BitVecVal(int(address, 16), 256)]

            assert account.nonce == int(details["nonce"], 16)
            assert account.code.bytecode == details["code"][2:]

            for index, value in details["storage"].items():
                expected = int(value, 16)
                actual = account.storage[int(index, 16)]
                if isinstance(actual, Expression):
                    actual = actual.value
                    actual = 1 if actual is True else 0 if actual is False else actual
                else:
                    if type(actual) == bytes:
                        actual = int(binascii.b2a_hex(actual), 16)
                    elif type(actual) == str:
                        actual = int(actual, 16)
                assert actual == expected
