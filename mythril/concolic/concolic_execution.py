import json
import binascii

from datetime import datetime, timedelta
from typing import Dict, List, Any
from copy import deepcopy

from mythril.concolic.concrete_data import ConcreteData
from mythril.concolic.find_trace import concrete_execution
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.strategy.concolic import ConcolicStrategy
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.symbolic import execute_transaction
from mythril.laser.ethereum.transaction.transaction_models import tx_id_manager
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.ethereum.time_handler import time_handler
from mythril.support.support_args import args


def flip_branches(
    init_state: WorldState,
    concrete_data: ConcreteData,
    jump_addresses: List[str],
    trace: List,
) -> List[Dict[str, Dict[str, Any]]]:
    """
    Flips branches and prints the input required for branch flip

    :param concrete_data: Concrete data
    :param jump_addresses: Jump addresses to flip
    :param trace: trace to follow
    """
    tx_id_manager.restart_counter()
    output_list = []
    laser_evm = LaserEVM(
        execution_timeout=600, use_reachability_check=False, transaction_count=10
    )
    laser_evm.open_states = [deepcopy(init_state)]
    laser_evm.strategy = ConcolicStrategy(
        work_list=laser_evm.work_list,
        max_depth=100,
        trace=trace,
        flip_branch_addresses=jump_addresses,
    )

    time_handler.start_execution(laser_evm.execution_timeout)
    laser_evm.time = datetime.now()

    for transaction in concrete_data["steps"]:
        execute_transaction(
            laser_evm,
            callee_address=transaction["address"],
            caller_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            data=transaction["input"][2:],
        )

    if laser_evm.strategy.results:
        for addr in jump_addresses:
            output_list.append(laser_evm.strategy.results[addr])
    return output_list


def concolic_execution(
    concrete_data: ConcreteData, jump_addresses: List, solver_timeout=100000
) -> List[Dict[str, Dict[str, Any]]]:
    """
    Executes codes and prints input required to cover the branch flips
    :param input_file: Input file
    :param jump_addresses: Jump addresses to flip
    :param solver_timeout: Solver timeout

    """

    init_state, trace = concrete_execution(concrete_data)
    args.solver_timeout = solver_timeout
    output_list = flip_branches(
        init_state=init_state,
        concrete_data=concrete_data,
        jump_addresses=jump_addresses,
        trace=trace,
    )
    return output_list
