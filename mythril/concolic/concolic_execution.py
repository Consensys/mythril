import binascii
import json
from typing import Dict, List
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.svm import LaserEVM
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from mythril.laser.plugin.loader import LaserPluginLoader
from mythril.laser.smt import Expression, BitVec, symbol_factory
from mythril.laser.plugin.plugins import TraceFinderBuilder


def setup_initial_state(concolic_data: Dict) -> WorldState:
    world_state = WorldState()
    for address, details in concolic_data["accounts"]:
        account = Account(address, concrete_storage=True)
        account.code = Disassembly(details["code"][2:])
        account.nonce = int(details["nonce"], 16)
        for key, value in details["storage"].items():
            key_bitvec = symbol_factory.BitVecVal(int(key, 16), 256)
            account.storage[key_bitvec] = symbol_factory.BitVecVal(int(value, 16), 256)

        world_state.put_account(account)
        account.set_balance(int(details["balance"], 16))
    return world_state


def execute_concolic(init_state: WorldState, concolic_data: Dict) -> Dict:
    laser_evm = LaserEVM()
    laser_evm.open_states = [init_state]
    plugin_loader = LaserPluginLoader()
    trace_plugin = TraceFinderBuilder()
    plugin_loader.load(trace_plugin)
    for transaction in concolic_data["steps"]:
        states = execute_message_call(
            laser_evm,
            callee_address=symbol_factory.BitVecVal(
                int(transaction["address"], 16), 256
            ),
            caller_address=symbol_factory.BitVecVal(
                int(transaction["caller"], 16), 256
            ),
            origin_address=symbol_factory.BitVecVal(
                int(transaction["origin"], 16), 256
            ),
            code=transaction["code"][2:],
            gas_limit=int(transaction["gasLimit"], 16),
            data=binascii.a2b_hex(transaction["input"][2:]),
            gas_price=int(transaction["gasPrice"], 16),
            value=concolic_data,
            track_gas=False,
        )
        assert len(states) == 1
        laser_evm.open_states = states
    return trace_plugin.tx_trace


def concolic_execution(input_file: str, jump_addresses: List):
    with open(input_file) as f:
        concolic_data = json.load(f)

    init_state = setup_initial_state(concolic_data)
    get_trace = execute_concolic(init_state, concolic_data)
    print(get_trace)
