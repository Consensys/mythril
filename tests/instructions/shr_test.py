import pytest

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum.instructions import Instruction
from mythril.laser.ethereum.transaction.transaction_models import MessageCallTransaction
from mythril.laser.smt import symbol_factory, simplify, LShR


def get_state():
    world_state = WorldState()
    account = world_state.create_account(balance=10, address=101)
    account.code = Disassembly("60606040")
    environment = Environment(account, None, None, None, None, None)
    state = GlobalState(world_state, environment, None, MachineState(gas_limit=8000000))
    state.transaction_stack.append(
        (MessageCallTransaction(world_state=WorldState(), gas_limit=8000000), None)
    )
    return state


BVV = symbol_factory.BitVecVal
BV = symbol_factory.BitVecSym

test_data = (
    ([BVV(33, 256), BVV(4, 256)], BVV(2, 256)),
    ([BVV(1 << 100, 256), BVV(257, 256)], BVV(0, 256)),
    ([BVV(23233, 256), BVV(10, 256)], BVV(23233 // (1 << 10), 256)),
    ([BV("a", 256), BVV(270, 256)], 0),
    (
        [BV("a", 256), BV("b", 256)],
        LShR(BV("a", 256), BV("b", 256)),
    ),  # Current approximate specs
)


@pytest.mark.parametrize("inputs,output,", test_data)
def test_shr(inputs, output):
    # Arrange
    state = get_state()

    state.mstate.stack = inputs
    instruction = Instruction("shr", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert simplify(new_state.mstate.stack[-1]) == output


@pytest.mark.parametrize(
    # Cases: https://github.com/ethereum/EIPs/blob/master/EIPS/eip-145.md#shr-logical-shift-right
    "val1, val2, expected",
    (
        (
            "0x0000000000000000000000000000000000000000000000000000000000000001",
            "0x00",
            "0x0000000000000000000000000000000000000000000000000000000000000001",
        ),
        (
            "0x0000000000000000000000000000000000000000000000000000000000000001",
            "0x01",
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "0x8000000000000000000000000000000000000000000000000000000000000000",
            "0x01",
            "0x4000000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "0x8000000000000000000000000000000000000000000000000000000000000000",
            "0xff",
            "0x0000000000000000000000000000000000000000000000000000000000000001",
        ),
        (
            "0x8000000000000000000000000000000000000000000000000000000000000000",
            "0x0100",
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "0x8000000000000000000000000000000000000000000000000000000000000000",
            "0x0101",
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "0x00",
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ),
        (
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "0x01",
            "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        ),
        (
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "0xff",
            "0x0000000000000000000000000000000000000000000000000000000000000001",
        ),
        (
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "0x0100",
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ),
        (
            "0x0000000000000000000000000000000000000000000000000000000000000000",
            "0x01",
            "0x0000000000000000000000000000000000000000000000000000000000000000",
        ),
    ),
)
def test_concrete_shr(val1, val2, expected):
    state = get_state()
    state.mstate.stack = [BVV(int(val1, 16), 256), BVV(int(val2, 16), 256)]
    expected = BVV(int(expected, 16), 256)
    instruction = Instruction("shr", dynamic_loader=None)

    # Act
    new_state = instruction.evaluate(state)[0]

    # Assert
    assert simplify(new_state.mstate.stack[-1]) == expected
