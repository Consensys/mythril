import unittest
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.callgraph import generate_graph
from mythril.ether.ethcontract import ETHContract


class SVMTestCase(unittest.TestCase):

    def runTest(self):

        code = "0x60606040525b603c5b60006010603e565b9050593681016040523660008237602060003683856040603f5a0204f41560545760206000f35bfe5b50565b005b73c3b2ae46792547a96b9f84405e36d0e07edcd05c5b905600a165627a7a7230582062a884f947232ada573f95940cce9c8bfb7e4e14e21df5af4e884941afb55e590029"

        contract = ETHContract(code)
        sym = SymExecWrapper([contract])

        html = generate_graph(sym)

        self.assertTrue("0 PUSH1 0x60\\n2 PUSH1 0x40\\n4 MSTORE\\n5 JUMPDEST" in html)
