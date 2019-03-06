from pathlib import Path
from mythril.mythril import MythrilDisassembler, MythrilAnalyzer
from mythril.analysis.report import Issue
from mock import patch


@patch("mythril.analysis.report.Issue.add_code_info", return_value=None)
@patch(
    "mythril.mythril.mythril_analyzer.fire_lasers",
    return_value=[Issue("", "", "234", "101", "title", "0x02445")],
)
@patch("mythril.mythril.mythril_analyzer.SymExecWrapper", return_value=None)
def test_fire_lasers(mock_sym, mock_fire_lasers, mock_code_info):
    disassembler = MythrilDisassembler(eth=None)
    disassembler.load_from_solidity(
        [
            str(
                (
                    Path(__file__).parent.parent / "testdata/input_contracts/origin.sol"
                ).absolute()
            )
        ]
    )
    analyzer = MythrilAnalyzer(disassembler, strategy="dfs")

    issues = analyzer.fire_lasers(modules=[]).sorted_issues()
    mock_sym.assert_called()
    mock_fire_lasers.assert_called()
    mock_code_info.assert_called()
    assert len(issues) == 1
    assert issues[0]["swc-id"] == "101"
