import logging
import re
import solc
import sys
import os
import platform

from ethereum import utils
from typing import List, Tuple, Optional
from mythril.ethereum import util
from mythril.ethereum.interface.rpc.client import EthJsonRpc
from mythril.exceptions import CriticalError, CompilerError, NoContractFoundError
from mythril.support import signatures
from mythril.ethereum.evmcontract import EVMContract
from mythril.ethereum.interface.rpc.exceptions import ConnectionError
from mythril.solidity.soliditycontract import SolidityContract, get_contracts_from_file

if sys.version_info[1] >= 6:
    import solcx

log = logging.getLogger(__name__)


class MythrilDisassembler:
    """
    The Mythril Disassembler class
    Responsible for generating disassembly of smart contracts
        - Compiles solc code from file/onchain
        - Can also be used to access onchain storage data
    """

    def __init__(
        self,
        eth: Optional[EthJsonRpc] = None,
        solc_version: str = None,
        solc_settings_json: str = None,
        enable_online_lookup: bool = False,
    ) -> None:
        self.solc_binary = self._init_solc_binary(solc_version)
        self.solc_settings_json = solc_settings_json
        self.eth = eth
        self.enable_online_lookup = enable_online_lookup
        self.sigs = signatures.SignatureDB(enable_online_lookup=enable_online_lookup)
        self.contracts = []  # type: List[EVMContract]

    @staticmethod
    def _init_solc_binary(version: str) -> str:
        """
        Only proper versions are supported. No nightlies, commits etc (such as available in remix).
        :param version: Version of the solc binary required
        :return: The solc binary of the corresponding version
        """

        if not version:
            return os.environ.get("SOLC") or "solc"

        # tried converting input to semver, seemed not necessary so just slicing for now
        main_version = solc.get_solc_version_string()

        # In case instead of just the version number, --solv v0.x.x is used

        if version.startswith("v"):
            version = version[1:]

        main_version_number = re.match(r"\d+.\d+.\d+", main_version)
        if main_version is None:
            raise CriticalError(
                "Could not extract solc version from string {}".format(main_version)
            )
        if version == main_version_number:
            log.info("Given version matches installed version")
            solc_binary = os.environ.get("SOLC") or "solc"
        else:
            solc_binary = util.solc_exists(version)
            if solc_binary is None:
                if sys.version_info[1] >= 6:
                    raise CriticalError(
                        "The version of solc that is needed cannot be installed automatically"
                    )
                elif sys.version_info[1] == 5:
                    raise CriticalError(
                        "Py-Solc doesn't support 0.5.*+. You can switch to python 3.6 which uses solcx."
                    )
                else:
                    raise CriticalError(
                        "There was an error when trying to install the specified solc version"
                    )
            else:
                log.info("Setting the compiler to %s", solc_binary)

        return solc_binary

    def load_from_bytecode(
        self, code: str, bin_runtime: bool = False, address: Optional[str] = None
    ) -> Tuple[str, EVMContract]:
        """
        Returns the address and the contract class for the given bytecode
        :param code: Bytecode
        :param bin_runtime: Whether the code is runtime code or creation code
        :param address: address of contract
        :return: tuple(address, Contract class)
        """
        if address is None:
            address = util.get_indexed_address(0)
        if bin_runtime:
            self.contracts.append(
                EVMContract(
                    code=code,
                    name="MAIN",
                    enable_online_lookup=self.enable_online_lookup,
                )
            )
        else:
            self.contracts.append(
                EVMContract(
                    creation_code=code,
                    name="MAIN",
                    enable_online_lookup=self.enable_online_lookup,
                )
            )
        return address, self.contracts[-1]  # return address and contract object

    def load_from_address(self, address: str) -> Tuple[str, EVMContract]:
        """
        Returns the contract given it's on chain address
        :param address: The on chain address of a contract
        :return: tuple(address, contract)
        """
        if not re.match(r"0x[a-fA-F0-9]{40}", address):
            raise CriticalError("Invalid contract address. Expected format is '0x...'.")

        if self.eth is None:
            raise CriticalError(
                "Please check whether the Infura key is set or use a different RPC method."
            )

        try:
            code = self.eth.eth_getCode(address)
        except FileNotFoundError as e:
            raise CriticalError("IPC error: " + str(e))
        except ConnectionError:
            raise CriticalError(
                "Could not connect to RPC server. Make sure that your node is running and that RPC parameters are set correctly."
            )
        except Exception as e:
            raise CriticalError("IPC / RPC error: " + str(e))

        if code == "0x" or code == "0x0":
            raise CriticalError(
                "Received an empty response from eth_getCode. Check the contract address and verify that you are on the correct chain."
            )
        else:
            self.contracts.append(
                EVMContract(
                    code, name=address, enable_online_lookup=self.enable_online_lookup
                )
            )
        return address, self.contracts[-1]  # return address and contract object

    def load_from_solidity(
        self, solidity_files: List[str]
    ) -> Tuple[str, List[SolidityContract]]:
        """

        :param solidity_files: List of solidity_files
        :return: tuple of address, contract class list
        """
        address = util.get_indexed_address(0)
        contracts = []
        for file in solidity_files:
            if ":" in file:
                file, contract_name = file.split(":")
            else:
                contract_name = None

            file = os.path.expanduser(file)

            try:
                # import signatures from solidity source
                self.sigs.import_solidity_file(
                    file,
                    solc_binary=self.solc_binary,
                    solc_settings_json=self.solc_settings_json,
                )
                if contract_name is not None:
                    contract = SolidityContract(
                        input_file=file,
                        name=contract_name,
                        solc_settings_json=self.solc_settings_json,
                        solc_binary=self.solc_binary,
                    )
                    self.contracts.append(contract)
                    contracts.append(contract)
                else:
                    for contract in get_contracts_from_file(
                        input_file=file,
                        solc_settings_json=self.solc_settings_json,
                        solc_binary=self.solc_binary,
                    ):
                        self.contracts.append(contract)
                        contracts.append(contract)

            except FileNotFoundError as e:
                raise CriticalError(f"Input file not found {e}")
            except CompilerError as e:
                error_msg = str(e)
                # Check if error is related to solidity version mismatch
                if (
                    "Error: Source file requires different compiler version"
                    in error_msg
                ):
                    # Grab relevant line "pragma solidity <solv>...", excluding any comments
                    solv_pragma_line = error_msg.split("\n")[-3].split("//")[0]
                    # Grab solidity version from relevant line
                    solv_match = re.findall(r"[0-9]+\.[0-9]+\.[0-9]+", solv_pragma_line)
                    error_suggestion = (
                        "<version_number>" if len(solv_match) != 1 else solv_match[0]
                    )
                    error_msg = (
                        error_msg
                        + '\nSolidityVersionMismatch: Try adding the option "--solv '
                        + error_suggestion
                        + '"\n'
                    )

                raise CriticalError(error_msg)
            except NoContractFoundError:
                log.error(
                    "The file " + file + " does not contain a compilable contract."
                )

        return address, contracts

    @staticmethod
    def hash_for_function_signature(func: str) -> str:
        """
        Return function names corresponding signature hash
        :param func: function name
        :return: Its hash signature
        """
        return "0x%s" % utils.sha3(func)[:4].hex()

    def get_state_variable_from_storage(
        self, address: str, params: Optional[List[str]] = None
    ) -> str:
        """
        Get variables from the storage
        :param address: The contract address
        :param params: The list of parameters
                        param types: [position, length] or ["mapping", position, key1, key2, ...  ]
                        or [position, length, array]
        :return: The corresponding storage slot and its value
        """
        params = params or []
        (position, length, mappings) = (0, 1, [])
        try:
            if params[0] == "mapping":
                if len(params) < 3:
                    raise CriticalError("Invalid number of parameters.")
                position = int(params[1])
                position_formatted = utils.zpad(utils.int_to_big_endian(position), 32)
                for i in range(2, len(params)):
                    key = bytes(params[i], "utf8")
                    key_formatted = utils.rzpad(key, 32)
                    mappings.append(
                        int.from_bytes(
                            utils.sha3(key_formatted + position_formatted),
                            byteorder="big",
                        )
                    )

                length = len(mappings)
                if length == 1:
                    position = mappings[0]

            else:
                if len(params) >= 4:
                    raise CriticalError("Invalid number of parameters.")

                if len(params) >= 1:
                    position = int(params[0])
                if len(params) >= 2:
                    length = int(params[1])
                if len(params) == 3 and params[2] == "array":
                    position_formatted = utils.zpad(
                        utils.int_to_big_endian(position), 32
                    )
                    position = int.from_bytes(
                        utils.sha3(position_formatted), byteorder="big"
                    )

        except ValueError:
            raise CriticalError(
                "Invalid storage index. Please provide a numeric value."
            )

        outtxt = []

        try:
            if length == 1:
                outtxt.append(
                    "{}: {}".format(
                        position, self.eth.eth_getStorageAt(address, position)
                    )
                )
            else:
                if len(mappings) > 0:
                    for i in range(0, len(mappings)):
                        position = mappings[i]
                        outtxt.append(
                            "{}: {}".format(
                                hex(position),
                                self.eth.eth_getStorageAt(address, position),
                            )
                        )
                else:
                    for i in range(position, position + length):
                        outtxt.append(
                            "{}: {}".format(
                                hex(i), self.eth.eth_getStorageAt(address, i)
                            )
                        )
        except FileNotFoundError as e:
            raise CriticalError("IPC error: " + str(e))
        except ConnectionError:
            raise CriticalError(
                "Could not connect to RPC server. "
                "Make sure that your node is running and that RPC parameters are set correctly."
            )
        return "\n".join(outtxt)
