import json

from typing import Dict, List
from mythril.laser.ethereum.strategy.basic import ConcolicStrategy
from mythril.laser.ethereum.svm import LaserEVM
from mythril.concolic.find_trace import concrete_execution


def flip_branches(concrete_data: Dict, jump_addresses: List, get_trace: List):
    """
    Flips branches and prints the input required for branch flip

    :param concrete_data: Concrete data
    :param jump_addresses: Jump addresses to flip
    :param get_trace: trace to follow
    """
    laser_evm = LaserEVM(execution_timeout=100, use_reachability_check=False)
    laser_evm.strategy = ConcolicStrategy(work_list=[], max_depth=None, trace=get_trace)


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
