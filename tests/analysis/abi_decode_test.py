import pytest

from mythril.analysis.report import Issue
from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.smt import symbol_factory, simplify, LShR


test_data = (
    (
        [
            "0xa9059cbb000000000000000000000000010801010101010120020101020401010408040401"
        ],
        "func(uint256, address)",
        ("0x0108010101010101200201010204010104080404",),
    ),
    ([BVV(1 << 100, 256), BVV(257, 256)], BVV(0, 256)),
    ([BVV(23233, 256), BVV(10, 256)], BVV(23233 // (1 << 10), 256)),
    ([BV("a", 256), BVV(270, 256)], 0),
    (
        [BV("a", 256), BV("b", 256)],
        LShR(BV("a", 256), BV("b", 256)),
    ),  # Current approximate specs
)


@pytest.mark.parametrize()
def test_abi_decode(call_data, signature, expected):
    assert Issue.add_signature(call_data, signature) == expected
