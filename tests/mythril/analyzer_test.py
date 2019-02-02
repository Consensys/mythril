import pytest
from pathlib import Path
from mythril.mythril import *

fire_lasers_execute = []


def fire_lasers_test():
    disassembler = MythrilDisassembler(eth=None)
    disassembler.load_from_solidity(
        Path(__file__).parent.parent / "testdata/input_contracts/origin.sol"
    )
    analyzer = MythrilAnalyzer(disassembler)
    issues = analyzer.fire_lasers(strategy="dfs").sorted_issues()
    assert len(issues) == 1
    assert issues["swc-id"] == "111"
