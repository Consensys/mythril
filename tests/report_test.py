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
    return report, input_file


@pytest.fixture(scope='module')
def reports():
    pool = Pool()
    input_files = [f for f in TESTDATA_INPUTS.iterdir()]
    results = pool.map(_generate_report, input_files)

    return results

def test_json(reports):
    changed_files = []
    for report, input_file in reports:
        output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".json")
        output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".json")

        output_current.write_text(_fix_path(_fix_debug_data(report.as_json())).strip())

        if not (output_expected.read_text() == output_current.read_text()):
            changed_files.append(str(input_file))

    assert len(changed_files) == 0, "Found changed files {}".format(changed_files)

def test_markdown(reports):
    changed_files = []
    for report, input_file in reports:
        output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".markdown")
        output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".markdown")

        output_current.write_text(_fix_path(report.as_markdown()))

        if not (output_expected.read_text() == output_current.read_text()):
            changed_files.append(str(input_file))

    assert len(changed_files) == 0, "Found changed files {}".format(changed_files)


def test_text(reports):
    changed_files = []
    for report, input_file in reports:
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".text")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".text")

            output_current.write_text(_fix_path(report.as_text()))

            if not (output_expected.read_text() == output_current.read_text()):
                changed_files.append(str(input_file))

    assert len(changed_files) == 0, "Found changed files {}".format(changed_files)
