from mythril.analysis.callgraph import generate_graph
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ethereum import util
from mythril.solidity.soliditycontract import EVMContract
from tests import (
    BaseTestCase,
    TESTDATA_INPUTS,
    TESTDATA_OUTPUTS_EXPECTED,
    TESTDATA_OUTPUTS_CURRENT,
)
import re


class GraphTest(BaseTestCase):
    def test_generate_graph(self):
        for input_file in TESTDATA_INPUTS.iterdir():
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (
                input_file.name + ".graph.html"
            )
            output_current = TESTDATA_OUTPUTS_CURRENT / (
                input_file.name + ".graph.html"
            )

            contract = EVMContract(input_file.read_text())

            sym = SymExecWrapper(
                contract,
                address=(util.get_indexed_address(0)),
                strategy="dfs",
                transaction_count=1,
                execution_timeout=5,
            )

            html = generate_graph(sym)
            output_current.write_text(html)

            lines_expected = re.findall(
                r"'label': '.*'", str(output_current.read_text())
            )
            lines_found = re.findall(r"'label': '.*'", str(output_current.read_text()))
            if not (lines_expected == lines_found):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()
