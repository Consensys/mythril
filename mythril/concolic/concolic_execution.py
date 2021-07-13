import json
import binascii
import sys

from datetime import datetime, timedelta
from typing import Dict, List
from copy import deepcopy

from mythril.concolic.find_trace import concrete_execution
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.strategy.concolic import (
    ConcolicStrategy,
    InvalidBranchException,
)
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.symbolic import execute_transaction
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.ethereum.time_handler import time_handler
from mythril.support.support_args import args


def flip_branches(
    init_state: WorldState, concrete_data: Dict, jump_addresses: List[str], trace: List
):
    """
    Flips branches and prints the input required for branch flip

    :param concrete_data: Concrete data
    :param jump_addresses: Jump addresses to flip
    :param trace: trace to follow
    """
    output_list = []
    for addr in jump_addresses:
        laser_evm = LaserEVM(
            execution_timeout=60, use_reachability_check=False, transaction_count=1
        )
        laser_evm.open_states = [deepcopy(init_state)]
        laser_evm.strategy = ConcolicStrategy(
            work_list=laser_evm.work_list,
            max_depth=100,
            trace=trace,
            flip_branch_addr=int(addr),
        )

        time_handler.start_execution(laser_evm.execution_timeout)
        laser_evm.time = datetime.now()

        for transaction in concrete_data["steps"]:
            try:
                execute_transaction(
                    laser_evm,
                    callee_address=transaction["address"],
                    caller_address=symbol_factory.BitVecVal(
                        int(transaction["origin"], 16), 256
                    ),
                    data=transaction["input"][2:],
                )
            except InvalidBranchException:
                break

        if laser_evm.strategy.results:
            output_list.append(laser_evm.strategy.results)
    json.dump(output_list, sys.stdout, indent=4)


def concolic_execution(concrete_data: Dict, jump_addresses: List):
    """
    Executes codes and prints input required to cover the branch flips
    :param input_file: Input file
    :param jump_addresses: Jump addresses to flip

    """
    init_state, trace = concrete_execution(concrete_data)
    args.solver_timeout = 50000
    flip_branches(
        init_state=init_state,
        concrete_data=concrete_data,
        jump_addresses=jump_addresses,
        trace=trace,
    )
