from unittest import TestCase
from pathlib import Path

from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import SolidityContract

TEST_FILES = Path(__file__).parent / "testdata"

def _fix_path(text):
    return text.replace(str(TEST_FILES), "<TEST_FILES>")

class AnalysisReportTest(TestCase):

    def test_reports(self):
        for input_file in TEST_FILES.iterdir():
            if input_file.is_file and input_file.suffix == '.sol':
                contract = SolidityContract(str(input_file), name=None, solc_args=None)
                sym = SymExecWrapper(contract, address=(util.get_indexed_address(0)))
                issues = fire_lasers(sym)

                for issue in issues:
                    issue.add_code_info(contract)

                report = Report()
                for issue in issues:
                    report.append_issue(issue)

                text = (TEST_FILES / (input_file.name + ".text")).read_text()
                json = (TEST_FILES / (input_file.name + ".json")).read_text()
                markdown = (TEST_FILES / (input_file.name + ".markdown")).read_text()

                self.assertEqual(_fix_path(report.as_text()), text)
                self.assertEqual(_fix_path(report.as_json()), json)
                self.assertEqual(_fix_path(report.as_markdown()), markdown)
