from mythril.solidity.soliditycontract import SolidityContract
from mythril.mythril import MythrilDisassembler
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.world_state import WorldState
from mythril.laser.ethereum import svm
from tests import BaseTestCase

SHA256_TEST = [(0, False) for _ in range(4)]
RIPEMD160_TEST = [(0, False) for _ in range(2)]
ECRECOVER_TEST = [(0, False) for _ in range(2)]
IDENTITY_TEST = [(0, False) for _ in range(2)]

# These are Random numbers to check whether the 'if condition' is entered or not
# (True means entered)
SHA256_TEST[0] = (hex(5555555555555555), True)
SHA256_TEST[1] = (hex(323232325445454546), False)
SHA256_TEST[2] = (hex(34756834765834658), True)
SHA256_TEST[3] = (hex(8756476956956795876987), False)

RIPEMD160_TEST[0] = (hex(999999999999999999993), True)
RIPEMD160_TEST[1] = (hex(1111111111112), False)

ECRECOVER_TEST[0] = (hex(674837568743979857398564869), True)
ECRECOVER_TEST[1] = (hex(3487683476979311), False)

IDENTITY_TEST[0] = (hex(87426857369875698), True)
IDENTITY_TEST[1] = (hex(476934798798347), False)


def _all_info(laser):
    nodes = {}
    for uid, node in laser.nodes.items():
        states = []
        for state in node.states:
            if isinstance(state, MachineState):
                states.append(state.as_dict)
            elif isinstance(state, GlobalState):
                environment = state.environment.as_dict
                environment["active_account"] = environment["active_account"].address
                states.append(
                    {
                        "accounts": state.accounts.keys(),
                        "environment": environment,
                        "mstate": state.mstate.as_dict,
                    }
                )

        nodes[uid] = {
            "uid": node.uid,
            "contract_name": node.contract_name,
            "start_addr": node.start_addr,
            "states": states,
            "constraints": node.constraints,
            "function_name": node.function_name,
            "flags": str(node.flags),
        }

    edges = [edge.as_dict for edge in laser.edges]

    return {
        "nodes": nodes,
        "edges": edges,
        "total_states": laser.total_states,
        "max_depth": laser.max_depth,
    }


def _test_natives(laser_info, test_list, test_name):
    for i, j in test_list:
        assert (str(i) in laser_info or str(int(i, 16)) in laser_info) == j


class NativeTests(BaseTestCase):
    @staticmethod
    def runTest():
        """"""
        disassembly = SolidityContract(
            "./tests/native_tests.sol",
            solc_binary=MythrilDisassembler._init_solc_binary("0.5.3"),
        ).disassembly
        account = Account("0x0000000000000000000000000000000000000000", disassembly)
        world_state = WorldState()
        world_state.put_account(account)
        laser = svm.LaserEVM(max_depth=100, transaction_count=1)
        laser.sym_exec(world_state=world_state, target_address=account.address.value)

        laser_info = str(_all_info(laser))

        _test_natives(laser_info, SHA256_TEST, "SHA256")
        _test_natives(laser_info, RIPEMD160_TEST, "RIPEMD160")
        _test_natives(laser_info, ECRECOVER_TEST, "ECRECOVER")
        _test_natives(laser_info, IDENTITY_TEST, "IDENTITY")
