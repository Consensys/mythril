import json
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.callgraph import generate_graph
from mythril.ether.ethcontract import ETHContract
from mythril.ether.soliditycontract import SolidityContract

from mythril.laser.ethereum.state import GlobalState, MachineState, Account
from mythril.laser.ethereum import svm
from tests import *


class LaserEncoder(json.JSONEncoder):
    def default(self, o):
        if getattr(o, "__module__", None) == "z3.z3":
            return str(o)
        return str(o)


def _all_info(laser):
    accounts = {}
    for address, _account in laser.world_state.accounts.items():
        account = _account.as_dict
        account["code"] = account["code"].instruction_list
        account['balance'] = str(account['balance'])
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
                states.append({
                    'accounts': state.accounts.keys(),
                    'environment': environment,
                    'mstate': state.mstate.as_dict
                })

        nodes[uid] = {
            'uid': node.uid,
            'contract_name': node.contract_name,
            'start_addr': node.start_addr,
            'states': states,
            'constraints': node.constraints,
            'function_name': node.function_name,
            'flags': str(node.flags)
        }

    edges = [edge.as_dict for edge in laser.edges]

    return {
        'accounts': accounts,
        'nodes': nodes,
        'edges': edges,
        'total_states': laser.total_states,
        'max_depth': laser.max_depth
    }


class SVMTestCase(BaseTestCase):

    def setUp(self):
        super(SVMTestCase, self).setUp()
        svm.gbl_next_uid = 0

    def test_laser_result(self):
        for input_file in TESTDATA_INPUTS_CONTRACTS.iterdir():
            if input_file.name in ["weak_random.sol", "environments.sol"]:
                continue
            output_expected = TESTDATA_OUTPUTS_EXPECTED_LASER_RESULT / (input_file.name + ".json")
            output_current = TESTDATA_OUTPUTS_CURRENT_LASER_RESULT / (input_file.name + ".json")

            disassembly = SolidityContract(str(input_file)).disassembly
            account = Account("0x0000000000000000000000000000000000000000", disassembly)
            accounts = {account.address: account}

            laser = svm.LaserEVM(accounts, max_depth=22)
            laser.sym_exec(account.address)
            laser_info = _all_info(laser)

            output_current.write_text(json.dumps(laser_info, cls=LaserEncoder, indent=4))

            if not (output_expected.read_text() == output_expected.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()

    def runTest(self):

        code = "0x60606040525b603c5b60006010603e565b9050593681016040523660008237602060003683856040603f5a0204f41560545760206000f35bfe5b50565b005b73c3b2ae46792547a96b9f84405e36d0e07edcd05c5b905600a165627a7a7230582062a884f947232ada573f95940cce9c8bfb7e4e14e21df5af4e884941afb55e590029"

        contract = ETHContract(code)
        sym = SymExecWrapper(contract, "0xd0a6E6C543bC68Db5db3A191B171A77407Ff7ccf")

        html = generate_graph(sym)

        self.assertTrue("0 PUSH1 0x60\\n2 PUSH1 0x40\\n4 MSTORE\\n5 JUMPDEST" in html)
