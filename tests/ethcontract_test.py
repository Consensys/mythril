import unittest
from mythril.ether.ethcontract import ETHContract


class ETHContractTestCase(unittest.TestCase):

    def setUp(self):
        self.code = "0x60606040525b603c5b60006010603e565b9050593681016040523660008237602060003683856040603f5a0204f41560545760206000f35bfe5b50565b005b73c3b2ae46792547a96b9f84405e36d0e07edcd05c5b905600a165627a7a7230582062a884f947232ada573f95940cce9c8bfb7e4e14e21df5af4e884941afb55e590029"

class GetDisassemblyTestCase(ETHContractTestCase):

    def runTest(self):

        contract = ETHContract(self.code)

        disassembly = contract.get_disassembly()

        self.assertEqual(len(disassembly), 71, 'Error disassembling code using ETHContract.get_disassembly()')

class GetEASMTestCase(ETHContractTestCase):

    def runTest(self):

        contract = ETHContract(self.code)

        disassembly = contract.get_easm()

        self.assertTrue("PUSH1 0x60" in disassembly,'Error obtaining EASM code through ETHContract.get_easm()')

class MatchesExpressionTestCase(ETHContractTestCase):

    def runTest(self):

        contract = ETHContract(self.code)

        self.assertTrue(contract.matches_expression("code#PUSH1# or code#PUSH1#"),'Unexpected result in expression matching')
        self.assertFalse(contract.matches_expression("func#abcdef#"),'Unexpected result in expression matching')

class GetXrefsTestCase(ETHContractTestCase):

    def runTest(self):

        contract = ETHContract(self.code)

        xrefs = contract.get_xrefs()

        self.assertEqual(xrefs[0], "c3b2ae46792547a96b9f84405e36d0e07edcd05c", 'Error getting xrefs from contract')