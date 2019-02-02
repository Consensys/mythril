from pathlib import Path
from mythril.mythril import MythrilDisassembler, MythrilAnalyzer


def test_fire_lasers():
    disassembler = MythrilDisassembler(eth=None)
    print(str((Path(__file__).parent.parent / "testdata/input_contracts/origin.sol")))
    print(Path(__file__))
    disassembler.load_from_solidity(
        [
            str(
                (
                    Path(__file__).parent.parent / "testdata/input_contracts/origin.sol"
                ).absolute()
            )
        ]
    )
    analyzer = MythrilAnalyzer(disassembler)
    issues = analyzer.fire_lasers(
        strategy="dfs", max_depth=30, transaction_count=2, create_timeout=10, modules=[]
    ).sorted_issues()
    assert len(issues) == 1
    assert issues[0]["swc-id"] == "111"
