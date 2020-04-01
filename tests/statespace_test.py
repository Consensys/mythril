from mythril.mythril import MythrilAnalyzer, MythrilDisassembler
from mythril.ethereum import util
from mythril.solidity.soliditycontract import EVMContract
from tests import TESTDATA_INPUTS


def test_statespace_dump():
    for input_file in TESTDATA_INPUTS.iterdir():
        if input_file.name not in ("origin.sol.o", "suicide.sol.o"):
            # It's too slow, so it's better to skip some tests.
            continue
        contract = EVMContract(input_file.read_text())
        disassembler = MythrilDisassembler()
        disassembler.contracts.append(contract)
        analyzer = MythrilAnalyzer(
            disassembler=disassembler,
            strategy="dfs",
            execution_timeout=5,
            max_depth=30,
            address=(util.get_indexed_address(0)),
            solver_timeout=10000,
        )

        analyzer.dump_statespace(contract=contract)
