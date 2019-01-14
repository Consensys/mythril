from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers, reset_callback_modules
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ethereum import util
from mythril.solidity.soliditycontract import EVMContract
from multiprocessing import Pool, cpu_count
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
    return json.dumps(read_json, sort_keys=True)


def _generate_report(input_file):
    contract = EVMContract(input_file.read_text(), enable_online_lookup=False)
    sym = SymExecWrapper(
        contract,
        address=(util.get_indexed_address(0)),
        strategy="dfs",
        execution_timeout=30,
        transaction_count=1,
    )
    issues = fire_lasers(sym)

    report = Report()
    for issue in issues:
        issue.filename = "test-filename.sol"
        report.append_issue(issue)
    return report, input_file


@pytest.fixture(scope="module")
def reports():
    """Fixture that analyses all reports."""
    reset_callback_modules()
    pool = Pool(cpu_count())
    input_files = sorted(
        [f for f in TESTDATA_INPUTS.iterdir() if f.name != "environments.sol.o"]
    )
    results = pool.map(_generate_report, input_files)

    return results


def _assert_empty(changed_files, postfix):
    """Asserts there are no changed files and otherwise builds error
    message."""
    message = ""
    for input_file in changed_files:
        output_expected = (
            (TESTDATA_OUTPUTS_EXPECTED / (input_file.name + postfix))
            .read_text()
            .splitlines(1)
        )
        output_current = (
            (TESTDATA_OUTPUTS_CURRENT / (input_file.name + postfix))
            .read_text()
            .splitlines(1)
        )

        difference = "".join(difflib.unified_diff(output_expected, output_current))
        message += "Found differing file for input: {} \n Difference: \n {} \n".format(
            str(input_file), str(difference)
        )

    assert message == "", message


def _assert_empty_json(changed_files, postfix=".json"):
    """Asserts there are no changed files and otherwise builds error
    message."""
    expected = []
    actual = []

    def ordered(obj):
        """

        :param obj:
        :return:
        """
        if isinstance(obj, dict):
            return sorted((k, ordered(v)) for k, v in obj.items())
        elif isinstance(obj, list):
            return sorted(ordered(x) for x in obj)
        else:
            return obj

    for input_file in changed_files:
        output_expected = json.loads(
            (TESTDATA_OUTPUTS_EXPECTED / (input_file.name + postfix)).read_text()
        )
        output_current = json.loads(
            (TESTDATA_OUTPUTS_CURRENT / (input_file.name + postfix)).read_text()
        )

        if not ordered(output_expected.items()) == ordered(output_current.items()):
            expected.append(output_expected)
            actual.append(output_current)
            print("Found difference in {}".format(str(input_file)))

    assert expected == actual


def _get_changed_files(postfix, report_builder, reports):
    """Returns a generator for all unexpected changes in generated reports.

    :param postfix: The applicable postfix
    :param report_builder: serialization function
    :param reports: The reports to serialize
    :return: Changed files
    """
    for report, input_file in reports:
        output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + postfix)
        output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + postfix)
        output_current.write_text(report_builder(report))
        if not (output_expected.read_text() == output_current.read_text()):
            yield input_file


def _get_changed_files_json(report_builder, reports, postfix=".json"):
    def ordered(obj):
        """

        :param obj:
        :return:
        """
        if isinstance(obj, dict):
            return sorted((k, ordered(v)) for k, v in obj.items())
        elif isinstance(obj, list):
            return sorted(ordered(x) for x in obj)
        else:
            return obj

    for report, input_file in reports:
        output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + postfix)
        output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + postfix)
        output_current.write_text(report_builder(report))

        if not ordered(json.loads(output_expected.read_text())) == ordered(
            json.loads(output_current.read_text())
        ):
            yield input_file


def test_json_report(reports):
    _assert_empty_json(
        _get_changed_files_json(
            lambda report: _fix_path(_fix_debug_data(report.as_json())).strip(), reports
        )
    )


def test_markdown_report(reports):
    _assert_empty(
        _get_changed_files(
            ".markdown", lambda report: _fix_path(report.as_markdown()), reports
        ),
        ".markdown",
    )


def test_text_report(reports):
    _assert_empty(
        _get_changed_files(
            ".text", lambda report: _fix_path(report.as_text()), reports
        ),
        ".text",
    )


def test_jsonv2_report(reports):
    _assert_empty_json(
        _get_changed_files_json(
            lambda report: _fix_path(report.as_swc_standard_format()).strip(),
            reports,
            ".jsonv2",
        ),
        ".jsonv2",
    )
