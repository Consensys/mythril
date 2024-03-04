import binascii
import json
import pathlib
import pytest
import subprocess

from copy import deepcopy
from datetime import datetime
from mock import patch
from subprocess import check_output, CalledProcessError
from tests import BaseTestCase, PROJECT_DIR, TESTDATA

from mythril.concolic import concrete_execution
from mythril.concolic.find_trace import setup_concrete_initial_state
from mythril.disassembler.asm import disassemble
from mythril.concolic.concrete_data import ConcreteData
from mythril.laser.ethereum import util

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.time_handler import time_handler
from mythril.laser.ethereum.transaction.concolic import execute_transaction
from mythril.laser.plugin.loader import LaserPluginLoader
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.plugin.plugins import TraceFinderBuilder

MYTH = str(PROJECT_DIR / "myth")


def output_of(command):
    try:
        return json.loads(check_output(command, shell=True).decode("UTF-8"))
    except CalledProcessError as exc:
        return json.loads(exc.output.decode("UTF-8"))


# TODO: Try using some python EVM for these tests


def validate_simple_example(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "153":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch_output["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 3


def validate_multiple_example(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "153":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch_output["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 3
        elif branch == "192":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch_output["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 5
        elif branch == "243":
            # Validation for initialState

            # Validation for tx steps
            tx_step = branch_output["steps"][1]
            assert tx_step["input"] == tx_step["calldata"]
            assert int(tx_step["input"][10:], 16) == 7


def validate_two_contract(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "311":

            # Validation for initialState
            # Validation for tx steps
            assert (
                int(branch_output["steps"][1]["input"][10:], 16)
                + int(branch_output["steps"][3]["input"][10:], 16)
                == 11
            )

        if branch == "341":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch_output["steps"][1]["input"][10:], 16)
                + int(branch_output["steps"][3]["input"][10:], 16)
                == 30
            )

        if branch == "371":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch_output["steps"][1]["input"][10:], 16)
                + int(branch_output["steps"][3]["input"][10:], 16)
                == 20
            )


def validate_multi_contract(output, branches):
    for branch_output, branch in zip(output, branches):
        if branch == "453":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch_output["steps"][1]["input"][10:], 16)
                + int(branch_output["steps"][3]["input"][10:], 16)
                + int(branch_output["steps"][5]["input"][10:], 16)
                == 10
            )

        if branch == "483":
            # Validation for initialState

            # Validation for tx steps
            assert (
                int(branch_output["steps"][1]["input"][10:], 16)
                + int(branch_output["steps"][3]["input"][10:], 16)
                + int(branch_output["steps"][5]["input"][10:], 16)
                == 25
            )


validate_test_data = (
    ("simple_example_input.json", validate_simple_example, "153"),
    ("multiple_example_input.json", validate_multiple_example, "153,192,243"),
    ("two_contract_input.json", validate_two_contract, "311,341,371"),
    ("multi_contract_example_input.json", validate_multi_contract, "453,483"),
)
check_state_validity_test_data = (
    ("simple_example_input.json", "153"),
    ("multiple_example_input.json", "153,192,243"),
    ("two_contract_input.json", "311,341,371"),
    ("multi_contract_example_input.json", "453,483"),
)

test_data_error = (("simple_example_input.json", "508"),)


@pytest.mark.parametrize("input_file,validate_function,branches", validate_test_data)
def test_concolic_conditions(input_file, validate_function, branches):
    input_path = str(TESTDATA / "concolic_io" / input_file)

    command = f"{MYTH} concolic {input_path} --branches {branches}"
    received_output = output_of(command)
    branches = [branch for branch in branches.split(",")]
    validate_function(received_output, branches)


@pytest.mark.parametrize("input_file,branch", test_data_error)
def test_concolic_error(input_file, branch):
    input_path = str(TESTDATA / "concolic_io" / input_file)
    command = f"{MYTH} concolic {input_path} --branches {branch}"
    received_output = subprocess.run(
        command.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )

    assert (
        f"The branch {branch} does not lead to a jump address, skipping this branch"
        in received_output.stderr.decode("UTF-8")
    )


def get_pc_from_disassembler(concrete_data, branches):
    init_state = setup_concrete_initial_state(concrete_data)
    laser_evm = LaserEVM(execution_timeout=100)

    laser_evm.open_states = [deepcopy(init_state)]
    plugin_loader = LaserPluginLoader()
    trace_plugin = TraceFinderBuilder()
    plugin_loader.load(trace_plugin)
    laser_evm.time = datetime.now()
    plugin_loader.instrument_virtual_machine(laser_evm, None)

    for transaction in concrete_data["steps"][:-1]:
        execute_transaction(
            laser_evm,
            callee_address=transaction["address"],
            caller_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            origin_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            gas_limit=int(transaction.get("gasLimit", "0x9999999999999999999999"), 16),
            data=binascii.a2b_hex(transaction["input"][2:]),
            gas_price=int(transaction.get("gasPrice", "0x773594000"), 16),
            value=int(transaction["value"], 16),
            track_gas=False,
        )
    contract_addr = concrete_data["steps"][-1]["address"]
    assert len(laser_evm.open_states) == 1
    instruction_list = (
        laser_evm.open_states[0].accounts[int(contract_addr, 16)].code.instruction_list
    )
    branches = [
        util.get_instruction_index(instruction_list, branch) for branch in branches
    ]
    return branches


def run_concolic(input_path, output, branches):
    with open(input_path) as f:
        concrete_data = json.load(f)
    _, input_trace = concrete_execution(concrete_data)
    input_last_tx = input_trace[-1]
    branches = [int(branch) for branch in branches.split(",")]
    time_handler.start_execution(1000)
    branches = get_pc_from_disassembler(concrete_data, branches)
    for out, branch in zip(output, branches):
        _, trace = concrete_execution(out)
        last_tx = trace[-1]
        tx_id = last_tx[0][1]
        branch_idx = last_tx.index((branch, tx_id))
        input_idx = input_last_tx.index((branch, tx_id))

        assert (branch_idx == input_idx) and last_tx[branch_idx + 1][
            0
        ] != input_last_tx[branch_idx + 1][0]


@pytest.mark.parametrize("input_file,branches", check_state_validity_test_data)
def test_validate_concolic_output(input_file, branches):
    input_path = str(TESTDATA / "concolic_io" / input_file)

    command = f"{MYTH} concolic {input_path} --branches {branches}"
    received_output = output_of(command)
    run_concolic(input_path, received_output, branches)
