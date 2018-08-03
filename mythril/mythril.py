#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""mythril.py: Bug hunting on the Ethereum blockchain

   http://www.github.com/b-mueller/mythril
"""

import logging
import json
import os
import re

from ethereum import utils
import codecs
from solc.exceptions import SolcError
import solc
from configparser import ConfigParser
import platform

from mythril.ether import util
from mythril.ether.ethcontract import ETHContract
from mythril.ether.soliditycontract import SolidityContract, get_contracts_from_file
from mythril.rpc.client import EthJsonRpc
from mythril.ipc.client import EthIpc
from mythril.rpc.exceptions import ConnectionError
from mythril.support import signatures
from mythril.support.truffle import analyze_truffle_project
from mythril.support.loader import DynLoader
from mythril.exceptions import CompilerError, NoContractFoundError, CriticalError
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.callgraph import generate_graph
from mythril.analysis.traceexplore import get_serializable_statespace
from mythril.analysis.security import fire_lasers
from mythril.analysis.report import Report
from mythril.leveldb.client import EthLevelDB

# logging.basicConfig(level=logging.DEBUG)

class Mythril(object):
    """
    Mythril main interface class.

    1. create mythril object
    2. set rpc or leveldb interface if needed
    3. load contracts (from solidity, bytecode, address)
    4. fire_lasers

    Example:
        mythril = Mythril()
        mythril.set_api_rpc_infura()

        # (optional) other API adapters
        mythril.set_api_rpc(args)
        mythril.set_api_ipc()
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
            print(mythril.graph_html(args))  # prints html or save it to file

        # (optional) other funcs
        mythril.dump_statespaces(args)
        mythril.disassemble(contract)
        mythril.get_state_variable_from_storage(args)

    """
    def __init__(self, solv=None,
                 solc_args=None, dynld=False):

        self.solv = solv
        self.solc_args = solc_args
        self.dynld = dynld

        self.mythril_dir = self._init_mythril_dir()

        self.sigs = signatures.SignatureDb()
        try:
            self.sigs.open()  # tries mythril_dir/signatures.json by default (provide path= arg to make this configurable)
        except FileNotFoundError as fnfe:
            logging.info(
                "No signature database found. Creating database if sigs are loaded in: " + self.sigs.signatures_file + "\n" +
                "Consider replacing it with the pre-initialized database at https://raw.githubusercontent.com/ConsenSys/mythril/master/signatures.json")
        except json.JSONDecodeError as jde:
            raise CriticalError("Invalid JSON in signatures file " + self.sigs.signatures_file + "\n" + str(jde))

        self.solc_binary = self._init_solc_binary(solv)
        self.config_path = os.path.join(self.mythril_dir, 'config.ini')
        self.leveldb_dir = self._init_config()

        self.eth = None # ethereum API client
        self.eth_db = None # ethereum LevelDB client

        self.contracts = []  # loaded contracts

    def _init_mythril_dir(self):
        try:
            mythril_dir = os.environ['MYTHRIL_DIR']
        except KeyError:
            mythril_dir = os.path.join(os.path.expanduser('~'), ".mythril")

            # Initialize data directory and signature database

        if not os.path.exists(mythril_dir):
            logging.info("Creating mythril data directory")
            os.mkdir(mythril_dir)
        return mythril_dir

    def _init_config(self):
        """
        If no config file exists, create it and add default options.
        Default LevelDB path is specified based on OS
        dynamic loading is set to infura by default in the file
        Returns: leveldb directory
        """

        system = platform.system().lower()
        leveldb_fallback_dir = os.path.expanduser('~')
        if system.startswith("darwin"):
            leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, "Library", "Ethereum")
        elif system.startswith("windows"):
            leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, "AppData", "Roaming", "Ethereum")
        else:
            leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, ".ethereum")
        leveldb_fallback_dir = os.path.join(leveldb_fallback_dir, "geth", "chaindata")

        if not os.path.exists(self.config_path):
            logging.info("No config file found. Creating default: " + self.config_path)
            open(self.config_path, 'a').close()

        config = ConfigParser(allow_no_value=True)
        config.optionxform = str
        config.read(self.config_path, 'utf-8')
        if 'defaults' not in config.sections():
            self._add_default_options(config)

        if not config.has_option('defaults', 'leveldb_dir'):
            self._add_leveldb_option(config, leveldb_fallback_dir)

        if not config.has_option('defaults', 'dynamic_loading'):
            self._add_dynamic_loading_option(config)

        with codecs.open(self.config_path, 'w', 'utf-8') as fp:
            config.write(fp)

        leveldb_dir = config.get('defaults', 'leveldb_dir', fallback=leveldb_fallback_dir)
        return os.path.expanduser(leveldb_dir)

    @staticmethod
    def _add_default_options(config):
        config.add_section('defaults')

    @staticmethod
    def _add_leveldb_option(config, leveldb_fallback_dir):
        config.set('defaults', "#Default chaindata locations:")
        config.set('defaults', "#– Mac: ~/Library/Ethereum/geth/chaindata")
        config.set('defaults', "#– Linux: ~/.ethereum/geth/chaindata")
        config.set('defaults', "#– Windows: %USERPROFILE%\\AppData\\Roaming\\Ethereum\\geth\\chaindata")
        config.set('defaults', 'leveldb_dir', leveldb_fallback_dir)

    @staticmethod
    def _add_dynamic_loading_option(config):
        config.set('defaults', '#– To connect to Infura use dynamic_loading: infura')
        config.set('defaults', '#– To connect to Ipc use dynamic_loading: ipc')
        config.set('defaults', '#– To connect to Rpc use '
                               'dynamic_loading: HOST:PORT / ganache / infura-[network_name]')
        config.set('defaults', '#– To connect to local host use dynamic_loading: localhost')
        config.set('defaults', 'dynamic_loading', 'infura')

    def analyze_truffle_project(self, *args, **kwargs):
        return analyze_truffle_project(self.sigs, *args, **kwargs)  # just passthru by passing signatures for now

    def _init_solc_binary(self, version):
        # Figure out solc binary and version
        # Only proper versions are supported. No nightlies, commits etc (such as available in remix)

        if version:
            # tried converting input to semver, seemed not necessary so just slicing for now
            if version == str(solc.main.get_solc_version())[:6]:
                logging.info('Given version matches installed version')
                try:
                    solc_binary = os.environ['SOLC']
                except KeyError:
                    solc_binary = 'solc'
            else:
                if util.solc_exists(version):
                    logging.info('Given version is already installed')
                else:
                    try:
                        solc.install_solc('v' + version)
                    except SolcError:
                        raise CriticalError("There was an error when trying to install the specified solc version")

                solc_binary = os.path.join(os.environ['HOME'], ".py-solc/solc-v" + version, "bin/solc")
                logging.info("Setting the compiler to " + str(solc_binary))
        else:
            try:
                solc_binary = os.environ['SOLC']
            except KeyError:
                solc_binary = 'solc'
        return solc_binary

    def set_api_leveldb(self, leveldb):
        self.eth_db = EthLevelDB(leveldb)
        self.eth = self.eth_db
        return self.eth

    def set_api_rpc_infura(self):
        self.eth = EthJsonRpc('mainnet.infura.io', 443, True)
        logging.info("Using INFURA for RPC queries")

    def set_api_rpc(self, rpc=None, rpctls=False):
        if rpc == 'ganache':
            rpcconfig = ('localhost', 7545, False)
        else:
            m = re.match(r'infura-(.*)', rpc)
            if m and m.group(1) in ['mainnet', 'rinkeby', 'kovan', 'ropsten']:
                rpcconfig = (m.group(1) + '.infura.io', 443, True)
            else:
                try:
                    host, port = rpc.split(":")
                    rpcconfig = (host, int(port), rpctls)
                except ValueError:
                    raise CriticalError("Invalid RPC argument, use 'ganache', 'infura-[network]' or 'HOST:PORT'")

        if rpcconfig:
            self.eth = EthJsonRpc(rpcconfig[0], int(rpcconfig[1]), rpcconfig[2])
            logging.info("Using RPC settings: %s" % str(rpcconfig))
        else:
            raise CriticalError("Invalid RPC settings, check help for details.")

    def set_api_ipc(self):
        try:
            self.eth = EthIpc()
        except Exception as e:
            raise CriticalError(
                "IPC initialization failed. Please verify that your local Ethereum node is running, or use the -i flag to connect to INFURA. \n" + str(
                    e))

    def set_api_rpc_localhost(self):
        self.eth = EthJsonRpc('localhost', 8545)
        logging.info("Using default RPC settings: http://localhost:8545")

    def set_api_from_config_path(self):
        config = ConfigParser(allow_no_value=False)
        config.optionxform = str
        config.read(self.config_path, 'utf-8')
        if config.has_option('defaults', 'dynamic_loading'):
            dynamic_loading = config.get('defaults', 'dynamic_loading')
        else:
            dynamic_loading = 'infura'
        if dynamic_loading == 'ipc':
            self.set_api_ipc()
        elif dynamic_loading == 'infura':
            self.set_api_rpc_infura()
        elif dynamic_loading == 'localhost':
            self.set_api_rpc_localhost()
        else:
            self.set_api_rpc(dynamic_loading)

    def search_db(self, search):

        def search_callback(contract, address, balance):

            print("Address: " + address + ", balance: " + str(balance))

        try:
            self.eth_db.search(search, search_callback)

        except SyntaxError:
            raise CriticalError("Syntax error in search expression.")

    def contract_hash_to_address(self, hash):
        if not re.match(r'0x[a-fA-F0-9]{64}', hash):
             raise CriticalError("Invalid address hash. Expected format is '0x...'.")

        print(self.eth_db.contract_hash_to_address(hash))

    def load_from_bytecode(self, code):
        address = util.get_indexed_address(0)
        self.contracts.append(ETHContract(code, name="MAIN"))
        return address, self.contracts[-1]  # return address and contract object

    def load_from_address(self, address):
        if not re.match(r'0x[a-fA-F0-9]{40}', address):
             raise CriticalError("Invalid contract address. Expected format is '0x...'.")

        try:
            code = self.eth.eth_getCode(address)
        except FileNotFoundError as e:
             raise CriticalError("IPC error: " + str(e))
        except ConnectionError as e:
            raise CriticalError("Could not connect to RPC server. Make sure that your node is running and that RPC parameters are set correctly.")
        except Exception as e:
             raise CriticalError("IPC / RPC error: " + str(e))
        else:
            if code == "0x" or code == "0x0":
                 raise CriticalError("Received an empty response from eth_getCode. Check the contract address and verify that you are on the correct chain.")
            else:
                self.contracts.append(ETHContract(code, name=address))
        return address, self.contracts[-1]  # return address and contract object

    def load_from_solidity(self, solidity_files):
        """
        UPDATES self.sigs!
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
                with open(file, encoding="utf-8") as f:
                    self.sigs.import_from_solidity_source(f.read())
                # Save updated function signatures
                self.sigs.write()  # dump signatures to disk (previously opened file or default location)

                if contract_name is not None:
                    contract = SolidityContract(file, contract_name, solc_args=self.solc_args)
                    self.contracts.append(contract)
                    contracts.append(contract)
                else:
                    for contract in get_contracts_from_file(file, solc_args=self.solc_args):
                        self.contracts.append(contract)
                        contracts.append(contract)


            except FileNotFoundError:
                raise CriticalError("Input file not found: " + file)
            except CompilerError as e:
                raise CriticalError(e)
            except NoContractFoundError:
                logging.info("The file " + file + " does not contain a compilable contract.")


        return address, contracts

    def dump_statespace(self, strategy, contract, address=None, max_depth=12):

        sym = SymExecWrapper(contract, address, strategy,
                             dynloader=DynLoader(self.eth) if self.dynld else None,
                             max_depth=max_depth)

        return get_serializable_statespace(sym)

    def graph_html(self, strategy, contract, address, max_depth=12, enable_physics=False, phrackify=False):
        sym = SymExecWrapper(contract, address, strategy,
                             dynloader=DynLoader(self.eth) if self.dynld else None,
                             max_depth=max_depth)
        return generate_graph(sym, physics=enable_physics, phrackify=phrackify)

    def fire_lasers(self, strategy, contracts=None, address=None,
                    modules=None,
                    verbose_report=False, max_depth=None, execution_timeout=None, ):

        all_issues = []
        for contract in (contracts or self.contracts):
            sym = SymExecWrapper(contract, address, strategy,
                                 dynloader=DynLoader(self.eth) if self.dynld else None,
                                 max_depth=max_depth, execution_timeout=execution_timeout)

            issues = fire_lasers(sym, modules)

            if type(contract) == SolidityContract:
                for issue in issues:
                    issue.add_code_info(contract)

            all_issues += issues

        # Finally, output the results
        report = Report(verbose_report)
        for issue in all_issues:
            report.append_issue(issue)

        return report

    def get_state_variable_from_storage(self, address, params=[]):
        (position, length, mappings) = (0, 1, [])
        try:
            if params[0] == "mapping":
                if len(params) < 3:
                     raise CriticalError("Invalid number of parameters.")
                position = int(params[1])
                position_formatted = utils.zpad(utils.int_to_big_endian(position), 32)
                for i in range(2, len(params)):
                    key = bytes(params[i], 'utf8')
                    key_formatted = utils.rzpad(key, 32)
                    mappings.append(int.from_bytes(utils.sha3(key_formatted + position_formatted), byteorder='big'))

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
                    position_formatted = utils.zpad(utils.int_to_big_endian(position), 32)
                    position = int.from_bytes(utils.sha3(position_formatted), byteorder='big')

        except ValueError:
             raise CriticalError("Invalid storage index. Please provide a numeric value.")

        outtxt = []

        try:
            if length == 1:
                outtxt.append("{}: {}".format(position, self.eth.eth_getStorageAt(address, position)))
            else:
                if len(mappings) > 0:
                    for i in range(0, len(mappings)):
                        position = mappings[i]
                        outtxt.append("{}: {}".format(hex(position), self.eth.eth_getStorageAt(address, position)))
                else:
                    for i in range(position, position + length):
                        outtxt.append("{}: {}".format(hex(i), self.eth.eth_getStorageAt(address, i)))
        except FileNotFoundError as e:
             raise CriticalError("IPC error: " + str(e))
        except ConnectionError as e:
            raise CriticalError("Could not connect to RPC server. Make sure that your node is running and that RPC parameters are set correctly.")
        return '\n'.join(outtxt)

    def disassemble(self, contract):
        return contract.get_easm()

    @staticmethod
    def hash_for_function_signature(sig):
        return "0x%s" % utils.sha3(sig)[:4].hex()
