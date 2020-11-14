import binascii
import json

from datetime import datetime
from typing import Dict, List
from mythril.disassembler.disassembly import Disassembly
from mythril.concolic.concolic_strategy import ConcolicStrategy
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.concolic import execute_transaction
from mythril.laser.plugin.loader import LaserPluginLoader
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.plugin.plugins import TraceFinderBuilder


def setup_initial_state(concolic_data: Dict) -> WorldState:
    world_state = WorldState()
    for address, details in concolic_data["initialState"]["accounts"].items():
        account = Account(address, concrete_storage=True)
        account.code = Disassembly(details["code"][2:])
        account.nonce = details["nonce"]
        for key, value in details["storage"].items():
            key_bitvec = symbol_factory.BitVecVal(int(key, 16), 256)
            account.storage[key_bitvec] = symbol_factory.BitVecVal(int(value, 16), 256)

        world_state.put_account(account)
        account.set_balance(int(details["balance"], 16))
    return world_state


def concrete_execution(concrete_data: Dict) -> Dict:
    init_state = setup_initial_state(concrete_data)
    laser_evm = LaserEVM(execution_timeout=100)
    laser_evm.open_states = [init_state]
    plugin_loader = LaserPluginLoader()
    trace_plugin = TraceFinderBuilder()
    plugin_loader.load(trace_plugin)
    laser_evm.time = datetime.now()
    plugin_loader.instrument_virtual_machine(laser_evm, None)
    for transaction in concrete_data["steps"]:
        states = execute_transaction(
            laser_evm,
            callee_address=transaction["address"],
            caller_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            origin_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            gas_limit=int(transaction["gasLimit"], 16),
            data=binascii.a2b_hex(transaction["input"][2:]),
            gas_price=int(transaction["gasPrice"], 16),
            value=int(transaction["value"], 16),
            track_gas=False,
        )
    return plugin_loader.plugin_list["trace-finder"].tx_trace


def flip_branches(concrete_data: Dict, jump_addresses: List, get_trace: Dict):
    init_state = setup_initial_state(concrete_data)
    laser_evm = LaserEVM(execution_timeout=100)
    laser_evm.strategy = ConcolicStrategy(
        work_list=[init_state], max_depth=None, trace=get_trace
    )


def concolic_execution(input_file: str, jump_addresses: List):
    with open(input_file) as f:
        concrete_data = json.load(f)
    get_trace = concrete_execution(concrete_data)
    flip_branches(concrete_data, jump_addresses, get_trace)
