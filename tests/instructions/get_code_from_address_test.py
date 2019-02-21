import pytest

from mythril.disassembler.disassembly import Disassembly
from mythril.laser.ethereum.state.environment import Environment
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.support.loader import DynLoader
from mythril.ethereum.interface.rpc.client import EthJsonRpc
from mythril.laser.ethereum.instructions import Instruction


def _get_global_state():
    active_account = Account("0x0", code=Disassembly("60606040"))
    passive_account = Account(
        "0x325345346564645654645", code=Disassembly("6060604061626364")
    )
    environment = Environment(active_account, None, None, None, None, None)
    world_state = WorldState()
    world_state.accounts = {
        "0x0": active_account,
        "0x325345346564645654645": passive_account,
    }
    return GlobalState(world_state, environment, None, MachineState(gas_limit=8000000))


@pytest.mark.parametrize(
    "addr, eth, code_len",
    [
        (
            "0xb09C477eCDAd49DD5Ac26c2C64914C3a6693843a",
            EthJsonRpc("rinkeby.infura.io", 443, True),
            1548,
        ),
        (
            "0x863DF6BFa4469f3ead0bE8f9F2AAE51c91A907b4",
            EthJsonRpc("mainnet.infura.io", 443, True),
            0,
        ),
        (
            "0x325345346564645654645",
            EthJsonRpc("mainnet.infura.io", 443, True),
            16,
        ),  # This contract tests Address Cache
    ],
)
def test_extraction(addr, eth, code_len):
    global_state = _get_global_state()
    dynamic_loader = DynLoader(eth=eth)
    instruction = Instruction("", dynamic_loader=dynamic_loader)
    code = instruction._get_code_from_address(global_state, addr)
    assert len(code) == code_len
