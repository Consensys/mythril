#!/usr/bin/env python3
# -*- coding: UTF-8 -*-
"""mythril.py: Bug hunting on the Ethereum blockchain

   http://www.github.com/b-mueller/mythril
"""

import logging
import json
import os
import re

from ethereum import utils
from solc.exceptions import SolcError
import solc

from mythril.ether import util
from mythril.ether.contractstorage import get_persistent_storage
from mythril.ether.ethcontract import ETHContract
from mythril.ether.soliditycontract import SolidityContract
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
        mythril.set_db_rpc_infura()

        # (optional) other db adapters
        mythril.set_db_rpc(args)
        mythril.set_db_ipc()
        mythril.set_db_rpc_localhost()

        # (optional) other func
        mythril.analyze_truffle_project(args)
        mythril.search_db(args)
        mythril.init_db()

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
                 address=None,
                 solc_args=None, dynld=False):

        self.solv = solv
        self.address = address
        self.solc_args = solc_args
        self.dynld = dynld

        self.mythril_dir = self._init_mythril_dir()
        self.signatures_file, self.sigs = self._init_signatures()
        self.solc_binary = self._init_solc_binary(solv)

        self.eth = None
        self.ethDb = None
        self.dbtype = None  # track type of db (rpc,ipc,leveldb) used

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

    def _init_signatures(self):

        # If no function signature file exists, create it. Function signatures from Solidity source code are added automatically.

        signatures_file = os.path.join(self.mythril_dir, 'signatures.json')

        sigs = {}
        if not os.path.exists(signatures_file):
            logging.info("No signature database found. Creating empty database: " + signatures_file + "\n" +
                         "Consider replacing it with the pre-initialized database at https://raw.githubusercontent.com/ConsenSys/mythril/master/signatures.json")
            with open(signatures_file, 'a') as f:
                json.dump({}, f)

        with open(signatures_file) as f:
            try:
                sigs = json.load(f)
            except json.JSONDecodeError as e:
                raise CriticalError("Invalid JSON in signatures file " + signatures_file + "\n" + str(e))
        return signatures_file, sigs

    def _update_signatures(self, jsonsigs):
        # Save updated function signatures
        with open(self.signatures_file, 'w') as f:
            json.dump(jsonsigs, f)

        self.sigs = jsonsigs

    def analyze_truffle_project(self, *args, **kwargs):
        return analyze_truffle_project(*args, **kwargs)  # just passthru for now

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

    def set_db_leveldb(self, leveldb):
        self.ethDb = EthLevelDB(leveldb)
        self.eth = self.ethDb
        self.dbtype = "leveldb"
        return self.eth

    def set_db_rpc_infura(self):
        self.eth = EthJsonRpc('mainnet.infura.io', 443, True)
        logging.info("Using INFURA for RPC queries")
        self.dbtype = "rpc"

    def set_db_rpc(self, rpc=None, rpctls=False):
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
            self.dbtype = "rpc"
            logging.info("Using RPC settings: %s" % str(rpcconfig))
        else:
            raise CriticalError("Invalid RPC settings, check help for details.")

    def set_db_ipc(self):
        try:
            self.eth = EthIpc()
            self.dbtype = "ipc"
        except Exception as e:
            raise CriticalError(
                "IPC initialization failed. Please verify that your local Ethereum node is running, or use the -i flag to connect to INFURA. \n" + str(
                    e))

    def set_db_rpc_localhost(self):
        self.eth = EthJsonRpc('localhost', 8545)
        self.dbtype = "rpc"
        logging.info("Using default RPC settings: http://localhost:8545")

    def search_db(self, search):

        def search_callback(code_hash, code, addresses, balances):
            print("Matched contract with code hash " + code_hash)
            for i in range(0, len(addresses)):
                print("Address: " + addresses[i] + ", balance: " + str(balances[i]))

        contract_storage, _ = get_persistent_storage(self.mythril_dir)
        try:
            if self.dbtype=="leveldb":
                contract_storage.search(search, search_callback)
            else:
                self.ethDB.search(search, search_callback)
        except SyntaxError:
            raise CriticalError("Syntax error in search expression.")

    def init_db(self):
        contract_storage, _ = get_persistent_storage(self.mythril_dir)
        try:
            contract_storage.initialize(self.eth)
        except FileNotFoundError as e:
             raise CriticalError("Error syncing database over IPC: " + str(e))
        except ConnectionError as e:
            raise CriticalError("Could not connect to RPC server. Make sure that your node is running and that RPC parameters are set correctly.")

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
                signatures.add_signatures_from_file(file, self.sigs)
                contract = SolidityContract(file, contract_name, solc_args=self.solc_args)
                logging.info("Analyzing contract %s:%s" % (file, contract.name))
            except FileNotFoundError:
                 raise CriticalError("Input file not found: " + file)
            except CompilerError as e:
                 raise CriticalError(e)
            except NoContractFoundError:
                logging.info("The file " + file + " does not contain a compilable contract.")
            else:
                self.contracts.append(contract)
                contracts.append(contract)

        self._update_signatures(self.sigs)
        return address, contracts

    def dump_statespaces(self, contracts=None, address=None, max_depth=12):
        statespaces = []

        for contract in (contracts or self.contracts):
            sym = SymExecWrapper(contract, address,
                                 dynloader=DynLoader(self.eth) if self.dynld else None,
                                 max_depth=max_depth)
            statespaces.append((contract, get_serializable_statespace(sym)))

        return statespaces

    def graph_html(self, contract, address, max_depth=12, enable_physics=False, phrackify=False):
        sym = SymExecWrapper(contract, address,
                             dynloader=DynLoader(self.eth) if self.dynld else None,
                             max_depth=max_depth)
        return generate_graph(sym, physics=enable_physics, phrackify=phrackify)

    def fire_lasers(self, contracts=None, address=None,
                    modules=None,
                    verbose_report=False, max_depth=12):

        all_issues = []
        for contract in (contracts or self.contracts):

            sym = SymExecWrapper(contract, address,
                                 dynloader=DynLoader(self.eth) if self.dynld else None,
                                 max_depth=max_depth)

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
