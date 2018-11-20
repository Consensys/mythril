from mythril.solidity.soliditycontract import SolidityContract
from mythril.laser.ethereum.state.account import Account
from mythril.laser.ethereum.state.machine_state import MachineState
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum import svm
from tests import *


SHA256_TEST = [(0, False) for _ in range(6)]

RIPEMD160_TEST = [(0, False) for _ in range(6)]

ECRECOVER_TEST = [(0, False) for _ in range(9)]

IDENTITY_TEST = [(0, False) for _ in range(4)]

SHA256_TEST[0] = (
    5555555555555555,
    True,
)  # These are Random numbers to check whether the 'if condition' is entered or not(True means entered)
SHA256_TEST[1] = (323232325445454546, True)
SHA256_TEST[2] = (34756834765834658, False)
SHA256_TEST[3] = (8756476956956795876987, True)
SHA256_TEST[4] = (5763467587689578369, True)
SHA256_TEST[5] = (948365957658767467857, False)

RIPEMD160_TEST[0] = (1242435356364, True)
RIPEMD160_TEST[1] = (6732648654386435, True)
RIPEMD160_TEST[2] = (97457657536546465, False)
RIPEMD160_TEST[3] = (56436346436456546, True)
RIPEMD160_TEST[4] = (999999999999999999993, True)
RIPEMD160_TEST[5] = (1111111111112, False)


ECRECOVER_TEST[0] = (786428768768632537676, True)
ECRECOVER_TEST[1] = (4897983476979346779638, False)
ECRECOVER_TEST[2] = (674837568743979857398564869, True)
ECRECOVER_TEST[3] = (3487683476979311, False)
ECRECOVER_TEST[4] = (853729594875984769847369, True)
ECRECOVER_TEST[5] = (83579382475972439587, False)
ECRECOVER_TEST[6] = (8437589437695876985769, True)
ECRECOVER_TEST[7] = (9486794873598347697596, False)
ECRECOVER_TEST[8] = (346934876983476, True)

IDENTITY_TEST[0] = (87426857369875698, True)
IDENTITY_TEST[1] = (476934798798347, False)

IDENTITY_TEST[2] = (7346948379483769, True)
IDENTITY_TEST[3] = (83269476937987, False)


def _all_info(laser):
    accounts = {}
    for address, _account in laser.world_state.accounts.items():
        account = _account.as_dict
        account["code"] = account["code"].instruction_list
        account["balance"] = str(account["balance"])
        accounts[address] = account

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
        "accounts": accounts,
        "nodes": nodes,
        "edges": edges,
        "total_states": laser.total_states,
        "max_depth": laser.max_depth,
    }


def _test_natives(laser_info, test_list, test_name):
    success = 0
    for i, j in test_list:
        if (str(i) in laser_info) == j:
            success += 1
        else:
            print("Failed: " + str(i) + " " + str(j))
    assert success == len(test_list)


class NativeTests(BaseTestCase):
    @staticmethod
    def runTest():
        disassembly = SolidityContract("./tests/native_tests.sol").disassembly
        account = Account("0x0000000000000000000000000000000000000000", disassembly)
        accounts = {account.address: account}

        laser = svm.LaserEVM(accounts, max_depth=100, transaction_count=1)
        laser.sym_exec(account.address)

        laser_info = str(_all_info(laser))
        print("\n")

        _test_natives(laser_info, SHA256_TEST, "SHA256")
        _test_natives(laser_info, RIPEMD160_TEST, "RIPEMD160")
        _test_natives(laser_info, ECRECOVER_TEST, "ECRECOVER")
        _test_natives(laser_info, IDENTITY_TEST, "IDENTITY")
