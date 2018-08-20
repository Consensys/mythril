from mythril.laser.ethereum.svm import LaserEVM
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.transaction.concolic import execute_message_call
from datetime import datetime
from z3 import is_true, simplify
from mythril.laser.ethereum.util import get_concrete_int

def test_arithmatic():
    laser = LaserEVM({})
    # pre
    laser.world_state.create_account(address="0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6", balance=0x0de0b6b3a7640000, concrete_storage={})
    laser.world_state.accounts["0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6"].code =\
        Disassembly("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fff"
                    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055")

    # Exec
    laser.time = datetime.now()
    execute_message_call(
        laser,
        callee_address="0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6",
        caller_address="0xcd1722f2947def4cf144679da39c4c32bdc35681",
        origin_address="0xcd1722f2947def4cf144679da39c4c32bdc35681",
        code="7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01600055",
        gas="0x0186a0",
        data=(),
        gas_price="0x5af3107a4000",
        value="0x0de0b6b3a7640000"
    )

    # Post
    assert len(laser.open_states) == 1
    world_state = laser.open_states[0]
    account = world_state['0x0f572e5295c57f15886f9b263e2f6d2d6c7b5ec6']
    value_to_check = get_concrete_int(account.storage[0x00])
    assert value_to_check == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
