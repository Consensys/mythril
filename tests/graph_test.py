from mythril.analysis.callgraph import generate_graph
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ether import util
from mythril.ether.soliditycontract import SolidityContract
from tests import *

class GraphTest(BaseTestCase):

    def test_generate_graph(self):
        for input_file in TESTDATA_INPUTS.iterdir():
            output_expected = TESTDATA_OUTPUTS_EXPECTED / (input_file.name + ".graph.html")
            output_current = TESTDATA_OUTPUTS_CURRENT / (input_file.name + ".graph.html")

            contract = SolidityContract(str(input_file), name=None, solc_args=None)
            sym = SymExecWrapper(contract, address=(util.get_indexed_address(0)))

            html = generate_graph(sym)
            output_current.write_text(html)

            if not (output_expected.read_text() == output_current.read_text()):
                self.found_changed_files(input_file, output_expected, output_current)

        self.assert_and_show_changed_files()
