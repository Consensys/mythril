import json
import binascii

from typing import Dict, List
from mythril.concolic.find_trace import concrete_execution
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.strategy.basic import ConcolicStrategy
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.symbolic import execute_transaction
from mythril.laser.smt import Expression, BitVec, symbol_factory


def flip_branches(concrete_data: Dict, jump_addresses: List, get_trace: List):
    """
    Flips branches and prints the input required for branch flip

    :param concrete_data: Concrete data
    :param jump_addresses: Jump addresses to flip
    :param get_trace: trace to follow
    """
    laser_evm = LaserEVM(execution_timeout=100, use_reachability_check=False)
    laser_evm.strategy = ConcolicStrategy(work_list=laser_evm.work_list, max_depth=None, trace=get_trace)
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
        print("EXECUTE")
        execute_transaction(
            laser_evm,
            callee_address=transaction["address"],
            caller_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            data=transaction["input"][2:],
            world_state=world_state,
        )
        print(laser_evm.open_states)


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
