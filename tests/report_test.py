from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import ETHContract
from multiprocessing import Pool
import datetime
import pytest
import json
from tests import *
import difflib


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
    return report, input_file


@pytest.fixture(scope='module')
def reports():
    pool = Pool()
    input_files = [f for f in TESTDATA_INPUTS.iterdir()][:5]
    results = pool.map(_generate_report, input_files)

    return results


def _assert_empty(changed_files):
    message = ""
    for input_file in changed_files:
        output_expected = (TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")).read_text().splitlines(1)
        output_current = (TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")).read_text().splitlines(1)

        difference = ''.join(difflib.unified_diff(output_expected, output_current))
        message += "Found differing file for input: {} \n Difference: \n {} \n".format(str(input_file), str(difference))

    assert message == "", message


def _get_changed_files(postfix, report_builder, reports):
    for report, input_file in reports:
        output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + postfix)
        output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + postfix)
        output_current.write_text(report_builder(report))

        if not (output_expected.read_text() == output_current.read_text()):
            yield input_file


def test_json_report(reports):
    report_builder = lambda report: _fix_path(_fix_debug_data(report.as_json())).strip()
    _assert_empty(_get_changed_files('.json', report_builder, reports))


def test_markdown_report(reports):
    report_builder = lambda report: _fix_path(report.as_markdown())
    _assert_empty(_get_changed_files('.json', report_builder, reports))


def test_text_report(reports):
    report_builder = lambda report: _fix_path(report.as_text())
    _assert_empty(_get_changed_files('.json', report_builder, reports))
