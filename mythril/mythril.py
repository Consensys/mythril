#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""mythril.py: Bug hunting on the Ethereum blockchain

   http://www.github.com/b-mueller/mythril
"""

import codecs
import logging
import os
import platform
import re
import traceback
from pathlib import Path
from shutil import copyfile
from configparser import ConfigParser

import solc
from ethereum import utils
from solc.exceptions import SolcError

from mythril.ethereum import util
from mythril.ethereum.evmcontract import EVMContract
from mythril.ethereum.interface.rpc.client import EthJsonRpc
from mythril.ethereum.interface.rpc.exceptions import ConnectionError
from mythril.solidity.soliditycontract import SolidityContract, get_contracts_from_file
from mythril.support import signatures
from mythril.support.source_support import Source
from mythril.support.loader import DynLoader
from mythril.exceptions import CompilerError, NoContractFoundError, CriticalError
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.callgraph import generate_graph
from mythril.analysis.traceexplore import get_serializable_statespace
from mythril.analysis.security import fire_lasers, retrieve_callback_issues
from mythril.analysis.report import Report
from mythril.support.truffle import analyze_truffle_project
from mythril.ethereum.interface.leveldb.client import EthLevelDB

log = logging.getLogger(__name__)


class Mythril(object):
    """Mythril main interface class.

    1. create mythril object
    2. set rpc or leveldb interface if needed
    3. load contracts (from solidity, bytecode, address)
    4. fire_lasers

    .. code-block:: python

        mythril = Mythril()
        mythril.set_api_rpc_infura()

        # (optional) other API adapters
        mythril.set_api_rpc(args)
        mythril.set_api_rpc_localhost()
        mythril.set_api_leveldb(path)

        # (optional) other func
        mythril.analyze_truffle_project(args)
        mythril.search_db(args)

        # load contract
        mythril.load_from_bytecode(bytecode)
        mythril.load_from_address(address)
        mythril.load_from_solidity(solidity_file)

        # analyze
        print(mythril.fire_lasers(args).as_text())

        # (optional) graph
        for contract in mythril.contracts:
            # prints html or save it to file
            print(mythril.graph_html(args))

        # (optional) other funcs
        mythril.dump_statespaces(args)
        mythril.disassemble(contract)
        mythril.get_state_variable_from_storage(args)
    """

    def __init__(
        self,
        solv=None,
        solc_args=None,
        dynld=False,
        enable_online_lookup=False,
        onchain_storage_access=True,
    ):

        self.solv = solv
        self.solc_args = solc_args
        self.dynld = dynld
        self.onchain_storage_access = onchain_storage_access
        self.enable_online_lookup = enable_online_lookup

        self.mythril_dir = self._init_mythril_dir()

        # tries mythril_dir/signatures.db by default (provide path= arg to make this configurable)
        self.sigs = signatures.SignatureDB(
            enable_online_lookup=self.enable_online_lookup
        )

        self.solc_binary = self._init_solc_binary(solv)
        self.config_path = os.path.join(self.mythril_dir, "config.ini")
        self.leveldb_dir = self._init_config()

        self.eth = None  # ethereum API client
        self.eth_db = None  # ethereum LevelDB client

        self.contracts = []  # loaded contracts

    @staticmethod
    def _init_mythril_dir():
        try:
            mythril_dir = os.environ["MYTHRIL_DIR"]
        except KeyError:
            mythril_dir = os.path.join(os.path.expanduser("~"), ".mythril")

        if not os.path.exists(mythril_dir):
            # Initialize data directory
            log.info("Creating mythril data directory")
            os.mkdir(mythril_dir)

        db_path = str(Path(mythril_dir) / "signatures.db")
        if not os.path.exists(db_path):
            # if the default mythril dir doesn't contain a signature DB
            # initialize it with the default one from the project root
            asset_dir = Path(__file__).parent / "support" / "assets"
            copyfile(str(asset_dir / "signatures.db"), db_path)

        return mythril_dir

    def _init_config(self):
        """If no config file exists, create it and add default options.

        Default LevelDB path is specified based on OS
        dynamic loading is set to infura by default in the file
        Returns: leveldb directory
        """

        system = platform.system().lower()
        leveldb_fallback_dir = os.path.expanduser("~")
        if system.startswith("darwin"):
            leveldb_fallback_dir = os.path.join(
                leveldb_fallback_dir, "Library", "Ethereum"
            )
        elif system.startswith("windows"):
            leveldb_fallback_dir = os.path.join(
                leveldb_fallback_dir, "AppData", "Roaming", "Ethereum"
            )
        else:
            leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, ".ethereum")
        leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, "geth", "chaindata")

        if not os.path.exists(self.config_path):
            log.info("No config file found. Creating default: " + self.config_path)
            open(self.config_path, "a").close()

        config = ConfigParser(allow_no_value=True)
        config.optionxform = str
        config.read(self.config_path, "utf-8")
        if "defaults" not in config.sections():
            self._add_default_options(config)

        if not config.has_option("defaults", "leveldb_dir"):
            self._add_leveldb_option(config, leveldb_fallback_dir)

        if not config.has_option("defaults", "dynamic_loading"):
            self._add_dynamic_loading_option(config)

        with codecs.open(self.config_path, "w", "utf-8") as fp:
            config.write(fp)

        leveldb_dir = config.get(
            "defaults", "leveldb_dir", fallback=leveldb_fallback_dir
        )
        return os.path.expanduser(leveldb_dir)

    @staticmethod
    def _add_default_options(config):
        config.add_section("defaults")

    @staticmethod
    def _add_leveldb_option(config, leveldb_fallback_dir):
        config.set("defaults", "#Default chaindata locations:")
        config.set("defaults", "#– Mac: ~/Library/Ethereum/geth/chaindata")
        config.set("defaults", "#– Linux: ~/.ethereum/geth/chaindata")
        config.set(
            "defaults",
            "#– Windows: %USERPROFILE%\\AppData\\Roaming\\Ethereum\\geth\\chaindata",
        )
        config.set("defaults", "leveldb_dir", leveldb_fallback_dir)

    @staticmethod
    def _add_dynamic_loading_option(config):
        config.set("defaults", "#– To connect to Infura use dynamic_loading: infura")
        config.set(
            "defaults",
            "#– To connect to Rpc use "
            "dynamic_loading: HOST:PORT / ganache / infura-[network_name]",
        )
        config.set(
            "defaults", "#– To connect to local host use dynamic_loading: localhost"
        )
        config.set("defaults", "dynamic_loading", "infura")

    def analyze_truffle_project(self, *args, **kwargs):
        """

        :param args:
        :param kwargs:
        :return:
        """
        return analyze_truffle_project(
            self.sigs, *args, **kwargs
        )  # just passthru by passing signatures for now

    @staticmethod
    def _init_solc_binary(version):
        """Figure out solc binary and version.

        Only proper versions are supported. No nightlies, commits etc (such as available in remix).
        """

        if not version:
            return os.environ.get("SOLC") or "solc"

        # tried converting input to semver, seemed not necessary so just slicing for now
        main_version = solc.main.get_solc_version_string()
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
            if solc_binary:
                log.info("Given version is already installed")
            else:
                try:
                    solc.install_solc("v" + version)
                    solc_binary = util.solc_exists(version)
                    if not solc_binary:
                        raise SolcError()
                except SolcError:
                    raise CriticalError(
                        "There was an error when trying to install the specified solc version"
                    )

            log.info("Setting the compiler to %s", solc_binary)

        return solc_binary

    def set_api_leveldb(self, leveldb):
        """

        :param leveldb:
        :return:
        """
        self.eth_db = EthLevelDB(leveldb)
        self.eth = self.eth_db
        return self.eth

    def set_api_rpc_infura(self):
        """Set the RPC mode to INFURA on mainnet."""
        self.eth = EthJsonRpc("mainnet.infura.io", 443, True)
        log.info("Using INFURA for RPC queries")

    def set_api_rpc(self, rpc=None, rpctls=False):
        """

        :param rpc:
        :param rpctls:
        """
        if rpc == "ganache":
            rpcconfig = ("localhost", 8545, False)
        else:
            m = re.match(r"infura-(.*)", rpc)
            if m and m.group(1) in ["mainnet", "rinkeby", "kovan", "ropsten"]:
                rpcconfig = (m.group(1) + ".infura.io", 443, True)
            else:
                try:
                    host, port = rpc.split(":")
                    rpcconfig = (host, int(port), rpctls)
                except ValueError:
                    raise CriticalError(
                        "Invalid RPC argument, use 'ganache', 'infura-[network]' or 'HOST:PORT'"
                    )

        if rpcconfig:
            self.eth = EthJsonRpc(rpcconfig[0], int(rpcconfig[1]), rpcconfig[2])
            log.info("Using RPC settings: %s" % str(rpcconfig))
        else:
            raise CriticalError("Invalid RPC settings, check help for details.")

    def set_api_rpc_localhost(self):
        """Set the RPC mode to a local instance."""
        self.eth = EthJsonRpc("localhost", 8545)
        log.info("Using default RPC settings: http://localhost:8545")

    def set_api_from_config_path(self):
        """Set the RPC mode based on a given config file."""
        config = ConfigParser(allow_no_value=False)
        config.optionxform = str
        config.read(self.config_path, "utf-8")
        if config.has_option("defaults", "dynamic_loading"):
            dynamic_loading = config.get("defaults", "dynamic_loading")
        else:
            dynamic_loading = "infura"
        if dynamic_loading == "infura":
            self.set_api_rpc_infura()
        elif dynamic_loading == "localhost":
            self.set_api_rpc_localhost()
        else:
            self.set_api_rpc(dynamic_loading)

    def search_db(self, search):
        """

        :param search:
        """

        def search_callback(_, address, balance):
            """

            :param _:
            :param address:
            :param balance:
            """
            print("Address: " + address + ", balance: " + str(balance))

        try:
            self.eth_db.search(search, search_callback)

        except SyntaxError:
            raise CriticalError("Syntax error in search expression.")

    def contract_hash_to_address(self, hash):
        """

        :param hash:
        """
        if not re.match(r"0x[a-fA-F0-9]{64}", hash):
            raise CriticalError("Invalid address hash. Expected format is '0x...'.")

        print(self.eth_db.contract_hash_to_address(hash))

    def load_from_bytecode(self, code, bin_runtime=False, address=None):
        """

        :param code:
        :param bin_runtime:
        :param address:
        :return:
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

    def load_from_address(self, address):
        """

        :param address:
        :return:
        """
        if not re.match(r"0x[a-fA-F0-9]{40}", address):
            raise CriticalError("Invalid contract address. Expected format is '0x...'.")

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
        else:
            if code == "0x" or code == "0x0":
                raise CriticalError(
                    "Received an empty response from eth_getCode. Check the contract address and verify that you are on the correct chain."
                )
            else:
                self.contracts.append(
                    EVMContract(
                        code,
                        name=address,
                        enable_online_lookup=self.enable_online_lookup,
                    )
                )
        return address, self.contracts[-1]  # return address and contract object

    def load_from_solidity(self, solidity_files):
        """

        :param solidity_files:
        :return:
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
                    file, solc_binary=self.solc_binary, solc_args=self.solc_args
                )
                if contract_name is not None:
                    contract = SolidityContract(
                        input_file=file,
                        name=contract_name,
                        solc_args=self.solc_args,
                        solc_binary=self.solc_binary,
                    )
                    self.contracts.append(contract)
                    contracts.append(contract)
                else:
                    for contract in get_contracts_from_file(
                        input_file=file,
                        solc_args=self.solc_args,
                        solc_binary=self.solc_binary,
                    ):
                        self.contracts.append(contract)
                        contracts.append(contract)

            except FileNotFoundError:
                raise CriticalError("Input file not found: " + file)
            except CompilerError as e:
                raise CriticalError(e)
            except NoContractFoundError:
                log.error(
                    "The file " + file + " does not contain a compilable contract."
                )

        return address, contracts

    def dump_statespace(
        self,
        strategy,
        contract,
        address=None,
        max_depth=None,
        execution_timeout=None,
        create_timeout=None,
        enable_iprof=False,
    ):
        """

        :param strategy:
        :param contract:
        :param address:
        :param max_depth:
        :param execution_timeout:
        :param create_timeout:
        :return:
        """
        sym = SymExecWrapper(
            contract,
            address,
            strategy,
            dynloader=DynLoader(
                self.eth,
                storage_loading=self.onchain_storage_access,
                contract_loading=self.dynld,
            ),
            max_depth=max_depth,
            execution_timeout=execution_timeout,
            create_timeout=create_timeout,
            enable_iprof=enable_iprof,
        )

        return get_serializable_statespace(sym)

    def graph_html(
        self,
        strategy,
        contract,
        address,
        max_depth=None,
        enable_physics=False,
        phrackify=False,
        execution_timeout=None,
        create_timeout=None,
        enable_iprof=False,
    ):
        """

        :param strategy:
        :param contract:
        :param address:
        :param max_depth:
        :param enable_physics:
        :param phrackify:
        :param execution_timeout:
        :param create_timeout:
        :return:
        """
        sym = SymExecWrapper(
            contract,
            address,
            strategy,
            dynloader=DynLoader(
                self.eth,
                storage_loading=self.onchain_storage_access,
                contract_loading=self.dynld,
            ),
            max_depth=max_depth,
            execution_timeout=execution_timeout,
            create_timeout=create_timeout,
            enable_iprof=enable_iprof,
        )
        return generate_graph(sym, physics=enable_physics, phrackify=phrackify)

    def fire_lasers(
        self,
        strategy,
        contracts=None,
        address=None,
        modules=None,
        verbose_report=False,
        max_depth=None,
        execution_timeout=None,
        create_timeout=None,
        transaction_count=None,
        enable_iprof=False,
    ):
        """

        :param strategy:
        :param contracts:
        :param address:
        :param modules:
        :param verbose_report:
        :param max_depth:
        :param execution_timeout:
        :param create_timeout:
        :param transaction_count:
        :return:
        """
        all_issues = []
        for contract in contracts or self.contracts:
            try:
                sym = SymExecWrapper(
                    contract,
                    address,
                    strategy,
                    dynloader=DynLoader(
                        self.eth,
                        storage_loading=self.onchain_storage_access,
                        contract_loading=self.dynld,
                    ),
                    max_depth=max_depth,
                    execution_timeout=execution_timeout,
                    create_timeout=create_timeout,
                    transaction_count=transaction_count,
                    modules=modules,
                    compulsory_statespace=False,
                    enable_iprof=enable_iprof,
                )
                issues = fire_lasers(sym, modules)
            except KeyboardInterrupt:
                log.critical("Keyboard Interrupt")
                issues = retrieve_callback_issues(modules)
            except Exception:
                log.critical(
                    "Exception occurred, aborting analysis. Please report this issue to the Mythril GitHub page.\n"
                    + traceback.format_exc()
                )
                issues = retrieve_callback_issues(modules)

            for issue in issues:
                issue.add_code_info(contract)

            all_issues += issues

        source_data = Source()
        source_data.get_source_from_contracts_list(self.contracts)
        # Finally, output the results
        report = Report(verbose_report, source_data)
        for issue in all_issues:
            report.append_issue(issue)

        return report

    def get_state_variable_from_storage(self, address, params=None):
        """

        :param address:
        :param params:
        :return:
        """
        if params is None:
            params = []
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
                "Could not connect to RPC server. Make sure that your node is running and that RPC parameters are set correctly."
            )
        return "\n".join(outtxt)

    @staticmethod
    def disassemble(contract):
        """

        :param contract:
        :return:
        """
        return contract.get_easm()

    @staticmethod
    def hash_for_function_signature(sig):
        """

        :param sig:
        :return:
        """
        return "0x%s" % utils.sha3(sig)[:4].hex()
