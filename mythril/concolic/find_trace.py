import json
import binascii

from copy import deepcopy
from datetime import datetime
from typing import Dict, List

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.concolic import execute_transaction
from mythril.laser.plugin.loader import LaserPluginLoader
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.plugin.plugins import TraceFinderBuilder


def setup_concrete_initial_state(concrete_data: Dict) -> WorldState:
    """
    Sets up concrete initial state
    :param concrete_data: Concrete data
    :return: initialised world state

    """
    world_state = WorldState()
    for address, details in concrete_data["initialState"]["accounts"].items():
        account = Account(address, concrete_storage=True)
        account.code = Disassembly(details["code"][2:])
        account.nonce = details["nonce"]
        for key, value in details["storage"].items():
            key_bitvec = symbol_factory.BitVecVal(int(key, 16), 256)
            account.storage[key_bitvec] = symbol_factory.BitVecVal(int(value, 16), 256)

        world_state.put_account(account)
        account.set_balance(int(details["balance"], 16))
    return world_state


def concrete_execution(concrete_data: Dict) -> List:
    """
    Executes code concretely to find the path to be followed by concolic executor
    :param concrete_data: Concrete data
    :return: path trace

    """
    init_state = setup_concrete_initial_state(concrete_data)
    laser_evm = LaserEVM(execution_timeout=100)
    laser_evm.open_states = [deepcopy(init_state)]
    plugin_loader = LaserPluginLoader()
    trace_plugin = TraceFinderBuilder()
    plugin_loader.load(trace_plugin)
    laser_evm.time = datetime.now()
    plugin_loader.instrument_virtual_machine(laser_evm, None)
    for transaction in concrete_data["steps"]:
        execute_transaction(
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

    return init_state, plugin_loader.plugin_list["trace-finder"].tx_trace  # type: ignore
