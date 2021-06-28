import json
import binascii

from datetime import datetime, timedelta
from typing import Dict, List

from mythril.concolic.find_trace import concrete_execution
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.strategy.concolic import ConcolicStrategy
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.symbolic import execute_transaction
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.ethereum.time_handler import time_handler


def flip_branches(concrete_data: Dict, jump_addresses: List, trace: List):
    """
    Flips branches and prints the input required for branch flip

    :param concrete_data: Concrete data
    :param jump_addresses: Jump addresses to flip
    :param trace: trace to follow
    """
    for addr in jump_addresses:
        laser_evm = LaserEVM(execution_timeout=10, use_reachability_check=False)
        laser_evm.strategy = ConcolicStrategy(
            work_list=laser_evm.work_list,
            max_depth=100,
            trace=trace,
            flip_branch_addr=addr,
        )

        time_handler.start_execution(laser_evm.execution_timeout)
        laser_evm.time = datetime.now()

        world_state = WorldState()
        for address, data in concrete_data["initialState"]["accounts"].items():
            account = world_state.create_account(
                balance=int(data["balance"], 16),
                address=int(address, 16),
                concrete_storage=True,
                code=Disassembly(data["code"]),
            )
            account.set_storage(data["storage"])

        for transaction in concrete_data["steps"]:
            execute_transaction(
                laser_evm,
                callee_address=transaction["address"],
                caller_address=symbol_factory.BitVecVal(
                    int(transaction["origin"], 16), 256
                ),
                data=transaction["input"][2:],
                world_state=world_state,
            )
        results = laser_evm.strategy.results
        print(results)


def concolic_execution(input_file: str, jump_addresses: List):
    """
    Executes codes and prints input required to cover the branch flips
    :param input_file: Input file
    :param jump_addresses: Jump addresses to flip

    """
    with open(input_file) as f:
        concrete_data = json.load(f)
    trace = concrete_execution(concrete_data)
    flip_branches(concrete_data, jump_addresses, trace)
