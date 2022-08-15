from subprocess import check_output, CalledProcessError
from tests import BaseTestCase, TESTDATA, PROJECT_DIR, TESTS_DIR
from mock import patch

MYTH = str(PROJECT_DIR / "myth")


def output_of(command):
    """

    :param command:
    :return:
    """
    try:
        return check_output(command, shell=True).decode("UTF-8")
    except CalledProcessError as exc:
        return exc.output.decode("UTF-8")


class CommandLineToolTestCase(BaseTestCase):
    def test_disassemble_code_correctly(self):
        command = "python3 {} disassemble --bin-runtime -c 0x5050".format(MYTH)
        self.assertIn("0 POP\n1 POP\n", output_of(command))

    def test_disassemble_solidity_file_correctly(self):
        solidity_file = str(TESTDATA / "input_contracts" / "metacoin.sol")
        command = "python3 {} disassemble {} --solv 0.5.0".format(MYTH, solidity_file)
        self.assertIn("2 PUSH1 0x40\n4 MSTORE", output_of(command))

    def test_hash_a_function_correctly(self):
        command = "python3 {} function-to-hash 'setOwner(address)'".format(MYTH)
        self.assertIn("0x13af4035\n", output_of(command))

    def test_failure_json(self):
        command = "python3 {} analyze doesnt_exist.sol -o json".format(MYTH)
        print(output_of(command))
        self.assertIn(""""success": false""", output_of(command))

    def test_failure_text(self):
        command = "python3 {} analyze doesnt_exist.sol".format(MYTH)
        assert output_of(command) == ""

    def test_failure_jsonv2(self):
        command = "python3 {} analyze doesnt_exist.sol -o jsonv2".format(MYTH)
        self.assertIn(""""level": "error""" "", output_of(command))

    def test_analyze(self):
        solidity_file = str(TESTDATA / "input_contracts" / "origin.sol")
        command = "python3 {} analyze {} --solv 0.5.0".format(MYTH, solidity_file)
        self.assertIn("115", output_of(command))

    def test_analyze_bytecode(self):
        solidity_file = str(TESTDATA / "inputs" / "origin.sol.o")
        command = "python3 {} analyze --bin-runtime -f {}".format(MYTH, solidity_file)
        self.assertIn("115", output_of(command))

    def test_invalid_args_iprof(self):
        solidity_file = str(TESTDATA / "input_contracts" / "origin.sol")
        command = "python3 {} analyze {} --enable-iprof -o json".format(
            MYTH, solidity_file
        )
        self.assertIn(""""success": false""", output_of(command))

    def test_only_epic(self):
        command = "python3 {} --epic".format(MYTH)
        # Just check for crashes
        output_of(command)

    ''''
    def test_storage(self):
        command = """python3 {} read-storage "438767356, 3" 0x76799f77587738bfeef09452df215b63d2cfb08a """.format(
            MYTH
        )
        self.assertIn("0x1a270efc", output_of(command))
    '''


"""
class InfuraTestCase(BaseTestCase):
    def test_infura_mainnet(self):
        command = "python3 {} disassemble --rpc infura-mainnet  -a 0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208".format(
            MYTH
        )
        output = output_of(command)
        self.assertIn("0 PUSH1 0x60\n2 PUSH1 0x40\n4 MSTORE", output)
        self.assertIn("7278 POP\n7279 POP\n7280 JUMP\n7281 STOP", output)

    def test_infura_rinkeby(self):
        command = "python3 {} disassemble --rpc infura-rinkeby -a 0xB6f2bFED892a662bBF26258ceDD443f50Fa307F5".format(
            MYTH
        )
        output = output_of(command)
        self.assertIn("34 JUMPDEST\n35 CALLVALUE", output)

    def test_infura_kovan(self):
        command = "python3 {} disassemble --rpc infura-kovan -a 0xE6bBF9B5A3451242F82f8cd458675092617a1235".format(
            MYTH
        )
        output = output_of(command)
        self.assertIn("9999 PUSH1 0x00\n10001 NOT\n10002 AND\n10003 PUSH1 0x00", output)

    def test_infura_ropsten(self):
        command = "python3 {} disassemble --rpc infura-ropsten -a 0x6e0E0e02377Bc1d90E8a7c21f12BA385C2C35f78".format(
            MYTH
        )
        output = output_of(command)
        self.assertIn("1821 PUSH1 0x01\n1823 PUSH2 0x070c", output)
"""
