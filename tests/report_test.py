from unittest import TestCase
from pathlib import Path

from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import SolidityContract
import json

TEST_FILES = Path(__file__).parent / "testdata"

def _fix_path(text):
    return text.replace(str(TEST_FILES), "<TEST_FILES>")

def _fix_debug_data(json_str):
    read_json = json.loads(json_str)
    for issue in read_json["issues"]:
        issue["debug"] = "<DEBUG-DATA>"
    return json.dumps(read_json)

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

                # (TEST_FILES / (input_file.name + ".text")).write_text(_fix_path(report.as_text()))
                # (TEST_FILES / (input_file.name + ".json")).write_text(_fix_path(_fix_debug_data(report.as_json())))
                # (TEST_FILES / (input_file.name + ".markdown")).write_text(_fix_path(report.as_markdown()))

                text = (TEST_FILES / (input_file.name + ".text")).read_text()
                json_report = (TEST_FILES / (input_file.name + ".json")).read_text()
                markdown = (TEST_FILES / (input_file.name + ".markdown")).read_text()

                self.assertEqual(_fix_path(report.as_text()), text, "{}: text report is changed".format(str(input_file)))
                self.assertEqual(_fix_path(report.as_markdown()), markdown, "{}: markdown report is changed".format(str(input_file)))
                self.assertEqual(_fix_path(_fix_debug_data(report.as_json())), json_report, "{}: json report is changed".format(str(input_file)))
