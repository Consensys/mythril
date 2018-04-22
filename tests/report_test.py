from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import ETHContract

import json
from tests import *

def _fix_path(text):
    return text.replace(str(TESTDATA), "<TESTDATA>")

def _fix_debug_data(json_str):
    read_json = json.loads(json_str)
    for issue in read_json["issues"]:
        issue["debug"] = "<DEBUG-DATA>"
    return json.dumps(read_json, indent=4)

def _generate_report(input_file):
    contract = ETHContract(input_file.read_text())
    sym = SymExecWrapper(contract, address=(util.get_indexed_address(0)))
    issues = fire_lasers(sym)

    report = Report()
    for issue in issues:
        issue.filename = "test-filename.sol"
        report.append_issue(issue)

    return report

class AnalysisReportTest(BaseTestCase):

    def test_json_reports(self):
        for input_file in TESTDATA_INPUTS.iterdir():
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")

            report = _generate_report(input_file)
            output_current.write_text(_fix_path(_fix_debug_data(report.as_json())).strip())

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()

    def test_markdown_reports(self):
        for input_file in TESTDATA_INPUTS.iterdir():
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".markdown")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".markdown")

            report = _generate_report(input_file)
            output_current.write_text(_fix_path(report.as_markdown()))

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()

    def test_text_reports(self):
        for input_file in TESTDATA_INPUTS.iterdir():
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".text")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".text")

            report = _generate_report(input_file)
            output_current.write_text(_fix_path(report.as_text()))

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()
