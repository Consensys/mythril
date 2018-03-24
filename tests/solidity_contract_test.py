from unittest import TestCase
from pathlib import Path

from mythril.ether.soliditycontract import SolidityContract

TEST_FILES = Path(__file__).parent / "testdata"

class SolidityContractTest(TestCase):

    def test_get_source_info_without_name_gets_latest_contract_info(self):
        input_file = TEST_FILES / "multi_contracts.sol"
        contract = SolidityContract(str(input_file))

        code_info = contract.get_source_info(142)

        self.assertEqual(code_info.filename, str(input_file))
        self.assertEqual(code_info.lineno, 14)
        self.assertEqual(code_info.code, "msg.sender.transfer(2 ether)")

    def test_get_source_info_with_contract_name_specified(self):
        input_file = TEST_FILES / "multi_contracts.sol"
        contract = SolidityContract(str(input_file), name="Transfer1")

        code_info = contract.get_source_info(142)

        self.assertEqual(code_info.filename, str(input_file))
        self.assertEqual(code_info.lineno, 6)
        self.assertEqual(code_info.code, "msg.sender.transfer(1 ether)")
