from pathlib import Path

from mythril.ether.soliditycontract import SolidityContract
from tests import BaseTestCase

TEST_FILES = Path(__file__).parent / "testdata/input_contracts"


class SolidityContractTest(BaseTestCase):
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

    def test_get_source_info_with_contract_name_specified_constructor(self):
        input_file = TEST_FILES / "constructor_assert.sol"
        contract = SolidityContract(str(input_file), name="AssertFail")

        code_info = contract.get_source_info(62, constructor=True)

        self.assertEqual(code_info.filename, str(input_file))
        self.assertEqual(code_info.lineno, 6)
        self.assertEqual(code_info.code, "assert(var1>0)")
