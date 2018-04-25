from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import ETHContract
from multiprocessing import Pool
import datetime

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
    begin = datetime.datetime.now()
    contract = ETHContract(input_file.read_text())
    sym = SymExecWrapper(contract, address=(util.get_indexed_address(0)))
    issues = fire_lasers(sym)

    report = Report()
    for issue in issues:
        issue.filename = "test-filename.sol"
        report.append_issue(issue)
    end = datetime.datetime.now()
    print("Performing analysis on {} duration {}".format(input_file, end - begin))
    return report

class AnalysisReportTest(BaseTestCase):

    def setUp(self):
        super(AnalysisReportTest, self).setUp()
        pool = Pool(8)

        input_files = [f for f in TESTDATA_INPUTS.iterdir()]
        self.results = zip(pool.map(_generate_report, input_files), input_files)


    def test_json_reports(self):
        for report, input_file in self.results:
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")

            output_current.write_text(_fix_path(_fix_debug_data(report.as_json())).strip())

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()

    def test_markdown_reports(self):
        for report, input_file in self.results:
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")

            output_current.write_text(_fix_path(_fix_debug_data(report.as_markdown())).strip())

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()

    def test_text_reports(self):
        for report, input_file in self.results:
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")

            output_current.write_text(_fix_path(_fix_debug_data(report.as_text())).strip())

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)
        self.assert_and_show_changed_files()
