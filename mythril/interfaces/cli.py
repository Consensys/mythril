#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""mythril.py: Bug hunting on the Ethereum blockchain

   http://www.github.com/ConsenSys/mythril
"""

import argparse
import json
import logging
import os
import sys

import coloredlogs
import traceback

import mythril.support.signatures as sigs
from argparse import ArgumentParser, Namespace, RawTextHelpFormatter
from mythril.exceptions import (
    DetectorNotFoundError,
    CriticalError,
)
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.plugin.loader import MythrilPluginLoader
from mythril.mythril import MythrilAnalyzer, MythrilDisassembler, MythrilConfig

from mythril.analysis.module import ModuleLoader
from mythril.analysis.report import Report

from mythril.__version__ import __version__ as VERSION

# Initialise core Mythril Component
_ = MythrilPluginLoader()

ANALYZE_LIST = ("analyze", "a")
DISASSEMBLE_LIST = ("disassemble", "d")
SAFE_FUNCTIONS_COMMAND = "safe-functions"
READ_STORAGE_COMNAND = "read-storage"
FUNCTION_TO_HASH_COMMAND = "function-to-hash"
HASH_TO_ADDRESS_COMMAND = "hash-to-address"
LIST_DETECTORS_COMMAND = "list-detectors"
VERSION_COMMAND = "version"
HELP_COMMAND = "help"

log = logging.getLogger(__name__)

COMMAND_LIST = (
    ANALYZE_LIST
    + DISASSEMBLE_LIST
    + (
        READ_STORAGE_COMNAND,
        SAFE_FUNCTIONS_COMMAND,
        FUNCTION_TO_HASH_COMMAND,
        HASH_TO_ADDRESS_COMMAND,
        LIST_DETECTORS_COMMAND,
        VERSION_COMMAND,
        HELP_COMMAND,
    )
)


def exit_with_error(format_, message):
    """
    Exits with error
    :param format_: The format of the message
    :param message: message
    """
    if format_ == "text" or format_ == "markdown":
        log.error(message)
    elif format_ == "json":
        result = {"success": False, "error": str(message), "issues": []}
        print(json.dumps(result))
    else:
        result = [
            {
                "issues": [],
                "sourceType": "",
                "sourceFormat": "",
                "sourceList": [],
                "meta": {"logs": [{"level": "error", "hidden": True, "msg": message}]},
            }
        ]
        print(json.dumps(result))
    sys.exit()


def get_runtime_input_parser() -> ArgumentParser:
    """
    Returns Parser which handles input
    :return: Parser which handles input
    """
    parser = ArgumentParser(add_help=False)
    parser.add_argument(
        "-a",
        "--address",
        help="pull contract from the blockchain",
        metavar="CONTRACT_ADDRESS",
    )
    parser.add_argument(
        "--bin-runtime",
        action="store_true",
        help="Only when -c or -f is used. Consider the input bytecode as binary runtime code, default being the contract creation bytecode.",
    )
    return parser


def get_creation_input_parser() -> ArgumentParser:
    """
    Returns Parser which handles input
    :return: Parser which handles input
    """
    parser = ArgumentParser(add_help=False)
    parser.add_argument(
        "-c",
        "--code",
        help='hex-encoded bytecode string ("6060604052...")',
        metavar="BYTECODE",
    )
    parser.add_argument(
        "-f",
        "--codefile",
        help="file containing hex-encoded bytecode string",
        metavar="BYTECODEFILE",
        type=argparse.FileType("r"),
    )
    return parser


def get_safe_functions_parser() -> ArgumentParser:
    """
    Returns Parser which handles checking for safe functions
    :return: Parser which handles checking for safe functions
    """
    parser = ArgumentParser(add_help=False)
    parser.add_argument(
        "-c",
        "--code",
        help='hex-encoded bytecode string ("6060604052...")',
        metavar="BYTECODE",
    )
    parser.add_argument(
        "-f",
        "--codefile",
        help="file containing hex-encoded bytecode string",
        metavar="BYTECODEFILE",
        type=argparse.FileType("r"),
    )
    return parser


def get_output_parser() -> ArgumentParser:
    """
    Get parser which handles output
    :return: Parser which handles output
    """
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument(
        "-o",
        "--outform",
        choices=["text", "markdown", "json", "jsonv2"],
        default="text",
        help="report output format",
        metavar="<text/markdown/json/jsonv2>",
    )
    return parser


def get_rpc_parser() -> ArgumentParser:
    """
    Get parser which handles RPC flags
    :return: Parser which handles rpc inputs
    """
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument(
        "--rpc",
        help="custom RPC settings",
        metavar="HOST:PORT / ganache / infura-[network_name]",
        default="infura-mainnet",
    )
    parser.add_argument(
        "--rpctls", type=bool, default=False, help="RPC connection over TLS"
    )
    parser.add_argument("--infura-id", help="set infura id for onchain analysis")

    return parser


def get_utilities_parser() -> ArgumentParser:
    """
    Get parser which handles utilities flags
    :return: Parser which handles utility flags
    """
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument(
        "--solc-json",
        help="Json for the optional 'settings' parameter of solc's standard-json input",
    )
    parser.add_argument(
        "--solv",
        help="specify solidity compiler version. If not present, will try to install it (Experimental)",
        metavar="SOLV",
    )
    return parser


def main() -> None:
    """The main CLI interface entry point."""

    rpc_parser = get_rpc_parser()
    utilities_parser = get_utilities_parser()
    runtime_input_parser = get_runtime_input_parser()
    creation_input_parser = get_creation_input_parser()
    output_parser = get_output_parser()
    parser = argparse.ArgumentParser(
        description="Security analysis of Ethereum smart contracts"
    )
    parser.add_argument("--epic", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument(
        "-v", type=int, help="log level (0-5)", metavar="LOG_LEVEL", default=2
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")
    safe_function_parser = subparsers.add_parser(
        SAFE_FUNCTIONS_COMMAND,
        help="Check functions which are completely safe using symbolic execution",
        parents=[
            rpc_parser,
            utilities_parser,
            creation_input_parser,
            runtime_input_parser,
            output_parser,
        ],
        formatter_class=RawTextHelpFormatter,
    )
    analyzer_parser = subparsers.add_parser(
        ANALYZE_LIST[0],
        help="Triggers the analysis of the smart contract",
        parents=[
            rpc_parser,
            utilities_parser,
            creation_input_parser,
            runtime_input_parser,
            output_parser,
        ],
        aliases=ANALYZE_LIST[1:],
        formatter_class=RawTextHelpFormatter,
    )
    create_safe_functions_parser(safe_function_parser)
    create_analyzer_parser(analyzer_parser)

    disassemble_parser = subparsers.add_parser(
        DISASSEMBLE_LIST[0],
        help="Disassembles the smart contract",
        aliases=DISASSEMBLE_LIST[1:],
        parents=[
            rpc_parser,
            utilities_parser,
            creation_input_parser,
            runtime_input_parser,
        ],
        formatter_class=RawTextHelpFormatter,
    )
    create_disassemble_parser(disassemble_parser)

    subparsers.add_parser(
        LIST_DETECTORS_COMMAND,
        parents=[output_parser],
        help="Lists available detection modules",
    )
    read_storage_parser = subparsers.add_parser(
        "read-storage",
        help="Retrieves storage slots from a given address through rpc",
        parents=[rpc_parser],
    )
    contract_func_to_hash = subparsers.add_parser(
        FUNCTION_TO_HASH_COMMAND, help="Returns the hash signature of the function"
    )
    contract_hash_to_addr = subparsers.add_parser(
        HASH_TO_ADDRESS_COMMAND,
        help="converts the hashes in the blockchain to ethereum address",
    )
    subparsers.add_parser(
        VERSION_COMMAND, parents=[output_parser], help="Outputs the version"
    )
    create_read_storage_parser(read_storage_parser)
    create_hash_to_addr_parser(contract_hash_to_addr)
    create_func_to_hash_parser(contract_func_to_hash)

    subparsers.add_parser(HELP_COMMAND, add_help=False)

    # Get config values

    args = parser.parse_args()
    parse_args_and_execute(parser=parser, args=args)


def create_disassemble_parser(parser: ArgumentParser):
    """
    Modify parser to handle disassembly
    :param parser:
    :return:
    """
    # Using nargs=* would the implementation below for getting code for both disassemble and analyze
    parser.add_argument(
        "solidity_files",
        nargs="*",
        help="Inputs file name and contract name. Currently supports a single contract\n"
        "usage: file1.sol:OptionalContractName",
    )


def create_read_storage_parser(read_storage_parser: ArgumentParser):
    """
    Modify parser to handle storage slots
    :param read_storage_parser:
    :return:
    """

    read_storage_parser.add_argument(
        "storage_slots",
        help="read state variables from storage index",
        metavar="INDEX,NUM_SLOTS,[array] / mapping,INDEX,[KEY1, KEY2...]",
    )
    read_storage_parser.add_argument(
        "address", help="contract address", metavar="ADDRESS"
    )


def create_func_to_hash_parser(parser: ArgumentParser):
    """
    Modify parser to handle func_to_hash command
    :param parser:
    :return:
    """
    parser.add_argument(
        "func_name", help="calculate function signature hash", metavar="SIGNATURE"
    )


def create_hash_to_addr_parser(hash_parser: ArgumentParser):
    """
    Modify parser to handle hash_to_addr command
    :param hash_parser:
    :return:
    """
    hash_parser.add_argument(
        "hash", help="Find the address from hash", metavar="FUNCTION_NAME"
    )


def add_graph_commands(parser: ArgumentParser):
    commands = parser.add_argument_group("commands")
    commands.add_argument("-g", "--graph", help="generate a control flow graph")
    commands.add_argument(
        "-j",
        "--statespace-json",
        help="dumps the statespace json",
        metavar="OUTPUT_FILE",
    )


def create_safe_functions_parser(parser: ArgumentParser):
    """
    The duplication exists between safe-functions and analyze as some of them have different default values.
    """
    parser.add_argument(
        "solidity_files",
        nargs="*",
        help="Inputs file name and contract name. \n"
        "usage: file1.sol:OptionalContractName file2.sol file3.sol:OptionalContractName",
    )

    options = parser.add_argument_group("options")

    options.add_argument(
        "-m",
        "--modules",
        help="Comma-separated list of security analysis modules",
        metavar="MODULES",
    )
    options.add_argument(
        "--max-depth",
        type=int,
        default=128,
        help="Maximum recursion depth for symbolic execution",
    )
    options.add_argument(
        "--call-depth-limit",
        type=int,
        default=10,
        help="Maximum call depth limit for symbolic execution",
    )

    options.add_argument(
        "--strategy",
        choices=["dfs", "bfs", "naive-random", "weighted-random"],
        default="bfs",
        help="Symbolic execution strategy",
    )
    options.add_argument(
        "-b",
        "--loop-bound",
        type=int,
        default=5,
        help="Bound loops at n iterations",
        metavar="N",
    )
    options.add_argument(
        "--execution-timeout",
        type=int,
        default=86400,
        help="The amount of seconds to spend on symbolic execution",
    )
    options.add_argument(
        "--solver-timeout",
        type=int,
        default=100000,
        help="The maximum amount of time(in milli seconds) the solver spends for queries from analysis modules",
    )
    options.add_argument(
        "--parallel-solving",
        action="store_true",
        help="Enable solving z3 queries in parallel",
    )
    options.add_argument(
        "--solver-log",
        help="Path to the directory for solver log",
        metavar="SOLVER_LOG",
    )

    options.add_argument(
        "-q",
        "--query-signature",
        action="store_true",
        help="Lookup function signatures through www.4byte.directory",
    )
    options.add_argument(
        "--create-timeout",
        type=int,
        default=10,
        help="The amount of seconds to spend on the initial contract creation",
    )

    options.add_argument(
        "--enable-iprof", action="store_true", help="enable the instruction profiler"
    )
    options.add_argument(
        "--enable-coverage-strategy",
        action="store_true",
        help="enable coverage based search strategy",
    )
    options.add_argument(
        "--custom-modules-directory",
        help="designates a separate directory to search for custom analysis modules",
        metavar="CUSTOM_MODULES_DIRECTORY",
    )
    options.add_argument(
        "--attacker-address",
        help="Designates a specific attacker address to use during analysis",
        metavar="ATTACKER_ADDRESS",
    )
    options.add_argument(
        "--creator-address",
        help="Designates a specific creator address to use during analysis",
        metavar="CREATOR_ADDRESS",
    )


def create_analyzer_parser(analyzer_parser: ArgumentParser):
    """
    Modify parser to handle analyze command
    :param analyzer_parser:
    :return:
    """
    analyzer_parser.add_argument(
        "solidity_files",
        nargs="*",
        help="Inputs file name and contract name. \n"
        "usage: file1.sol:OptionalContractName file2.sol file3.sol:OptionalContractName",
    )
    add_graph_commands(analyzer_parser)
    options = analyzer_parser.add_argument_group("options")
    options.add_argument(
        "-m",
        "--modules",
        help="Comma-separated list of security analysis modules",
        metavar="MODULES",
    )
    options.add_argument(
        "--max-depth",
        type=int,
        default=128,
        help="Maximum recursion depth for symbolic execution",
    )
    options.add_argument(
        "--call-depth-limit",
        type=int,
        default=3,
        help="Maximum call depth limit for symbolic execution",
    )

    options.add_argument(
        "--strategy",
        choices=["dfs", "bfs", "naive-random", "weighted-random"],
        default="bfs",
        help="Symbolic execution strategy",
    )
    options.add_argument(
        "-b",
        "--loop-bound",
        type=int,
        default=3,
        help="Bound loops at n iterations",
        metavar="N",
    )
    options.add_argument(
        "-t",
        "--transaction-count",
        type=int,
        default=2,
        help="Maximum number of transactions issued by laser",
    )
    options.add_argument(
        "--execution-timeout",
        type=int,
        default=86400,
        help="The amount of seconds to spend on symbolic execution",
    )
    options.add_argument(
        "--solver-timeout",
        type=int,
        default=10000,
        help="The maximum amount of time(in milli seconds) the solver spends for queries from analysis modules",
    )
    options.add_argument(
        "--create-timeout",
        type=int,
        default=10,
        help="The amount of seconds to spend on the initial contract creation",
    )
    options.add_argument(
        "--parallel-solving",
        action="store_true",
        help="Enable solving z3 queries in parallel",
    )
    options.add_argument(
        "--solver-log",
        help="Path to the directory for solver log",
        metavar="SOLVER_LOG",
    )
    options.add_argument(
        "--no-onchain-data",
        action="store_true",
        help="Don't attempt to retrieve contract code, variables and balances from the blockchain",
    )
    options.add_argument(
        "--sparse-pruning",
        action="store_true",
        help="Checks for reachability after the end of tx. Recommended for short execution timeouts < 1 min",
    )
    options.add_argument(
        "--unconstrained-storage",
        action="store_true",
        help="Default storage value is symbolic, turns off the on-chain storage loading",
    )

    options.add_argument(
        "--phrack", action="store_true", help="Phrack-style call graph"
    )
    options.add_argument(
        "--enable-physics", action="store_true", help="enable graph physics simulation"
    )
    options.add_argument(
        "-q",
        "--query-signature",
        action="store_true",
        help="Lookup function signatures through www.4byte.directory",
    )
    options.add_argument(
        "--enable-iprof", action="store_true", help="enable the instruction profiler"
    )
    options.add_argument(
        "--disable-dependency-pruning",
        action="store_true",
        help="Deactivate dependency-based pruning",
    )
    options.add_argument(
        "--enable-coverage-strategy",
        action="store_true",
        help="enable coverage based search strategy",
    )
    options.add_argument(
        "--custom-modules-directory",
        help="designates a separate directory to search for custom analysis modules",
        metavar="CUSTOM_MODULES_DIRECTORY",
    )
    options.add_argument(
        "--attacker-address",
        help="Designates a specific attacker address to use during analysis",
        metavar="ATTACKER_ADDRESS",
    )
    options.add_argument(
        "--creator-address",
        help="Designates a specific creator address to use during analysis",
        metavar="CREATOR_ADDRESS",
    )


def validate_args(args: Namespace):
    """
    Validate cli args
    :param args:
    :return:
    """
    if args.__dict__.get("v", False):
        if 0 <= args.v < 6:
            log_levels = [
                logging.NOTSET,
                logging.CRITICAL,
                logging.ERROR,
                logging.WARNING,
                logging.INFO,
                logging.DEBUG,
            ]
            coloredlogs.install(
                fmt="%(name)s [%(levelname)s]: %(message)s", level=log_levels[args.v]
            )
            logging.getLogger("mythril").setLevel(log_levels[args.v])
        else:
            exit_with_error(
                args.outform, "Invalid -v value, you can find valid values in usage"
            )
    if args.command in DISASSEMBLE_LIST and len(args.solidity_files) > 1:
        exit_with_error("text", "Only a single arg is supported for using disassemble")

    if args.command in ANALYZE_LIST:
        if args.query_signature and sigs.ethereum_input_decoder is None:
            exit_with_error(
                args.outform,
                "The --query-signature function requires the python package ethereum-input-decoder",
            )

        if args.enable_iprof and args.v < 4:
            exit_with_error(
                args.outform,
                "--enable-iprof must be used with -v LOG_LEVEL where LOG_LEVEL >= 4",
            )


def set_config(args: Namespace):
    """
    Set config based on args
    :param args:
    :return: modified config
    """
    config = MythrilConfig()
    if args.__dict__.get("infura_id", None):
        config.set_api_infura_id(args.infura_id)
    if (args.command in ANALYZE_LIST and not args.no_onchain_data) and not (
        args.rpc or args.i
    ):
        config.set_api_from_config_path()

    if args.__dict__.get("rpc", None):
        # Establish RPC connection if necessary
        config.set_api_rpc(rpc=args.rpc, rpctls=args.rpctls)

    return config


def load_code(disassembler: MythrilDisassembler, args: Namespace):
    """
    Loads code into disassembly and returns address
    :param disassembler:
    :param args:
    :return: Address
    """

    address = None
    if args.__dict__.get("code", False):
        # Load from bytecode
        code = args.code[2:] if args.code.startswith("0x") else args.code
        address, _ = disassembler.load_from_bytecode(code, args.bin_runtime)
    elif args.__dict__.get("codefile", False):
        bytecode = "".join([l.strip() for l in args.codefile if len(l.strip()) > 0])
        bytecode = bytecode[2:] if bytecode.startswith("0x") else bytecode
        address, _ = disassembler.load_from_bytecode(bytecode, args.bin_runtime)
    elif args.__dict__.get("address", False):
        # Get bytecode from a contract address
        address, _ = disassembler.load_from_address(args.address)
    elif args.__dict__.get("solidity_files", False):
        # Compile Solidity source file(s)
        if args.command in ANALYZE_LIST and args.graph and len(args.solidity_files) > 1:
            exit_with_error(
                args.outform,
                "Cannot generate call graphs from multiple input files. Please do it one at a time.",
            )
        address, _ = disassembler.load_from_solidity(
            args.solidity_files
        )  # list of files
    else:
        exit_with_error(
            args.__dict__.get("outform", "text"),
            "No input bytecode. Please provide EVM code via -c BYTECODE, -a ADDRESS, -f BYTECODE_FILE or <SOLIDITY_FILE>",
        )
    return address


def print_function_report(myth_disassembler: MythrilDisassembler, report: Report):
    """
    Prints the function report
    :param report: Mythril's report
    :return:
    """
    contract_data = {}
    for contract in myth_disassembler.contracts:
        contract_data[contract.name] = list(
            set(contract.disassembly.address_to_function_name.values())
        )

    for issue in report.issues.values():
        if issue.function in contract_data[issue.contract]:
            contract_data[issue.contract].remove(issue.function)

    for contract, function_list in contract_data.items():
        print(f"Contract {contract}: \n")
        print(
            f"""{len(function_list)} functions are deemed safe in this contract: {", ".join(function_list)}\n\n"""
        )


def execute_command(
    disassembler: MythrilDisassembler,
    address: str,
    parser: ArgumentParser,
    args: Namespace,
):
    """
    Execute command
    :param disassembler:
    :param address:
    :param parser:
    :param args:
    :return:
    """

    if args.command == "read-storage":
        storage = disassembler.get_state_variable_from_storage(
            address=address,
            params=[a.strip() for a in args.storage_slots.strip().split(",")],
        )
        print(storage)

    elif args.command in DISASSEMBLE_LIST:
        if disassembler.contracts[0].code:
            print("Runtime Disassembly: \n" + disassembler.contracts[0].get_easm())
        if disassembler.contracts[0].creation_code:
            print("Disassembly: \n" + disassembler.contracts[0].get_creation_easm())

    elif args.command == SAFE_FUNCTIONS_COMMAND:
        function_analyzer = MythrilAnalyzer(
            strategy=args.strategy,
            disassembler=disassembler,
            address=address,
            max_depth=args.max_depth,
            execution_timeout=args.execution_timeout,
            loop_bound=args.loop_bound,
            create_timeout=args.create_timeout,
            enable_iprof=args.enable_iprof,
            disable_dependency_pruning=True,
            use_onchain_data=False,
            solver_timeout=args.solver_timeout,
            parallel_solving=args.parallel_solving,
            custom_modules_directory=args.custom_modules_directory
            if args.custom_modules_directory
            else "",
            call_depth_limit=args.call_depth_limit,
            sparse_pruning=False,
            unconstrained_storage=True,
            solver_log=args.solver_log,
        )
        try:
            report = function_analyzer.fire_lasers(
                modules=[m.strip() for m in args.modules.strip().split(",")]
                if args.modules
                else None,
                transaction_count=1,
            )
            print_function_report(disassembler, report)
        except DetectorNotFoundError as e:
            exit_with_error("text", format(e))
        except CriticalError as e:
            exit_with_error("text", "Analysis error encountered: " + format(e))

    elif args.command in ANALYZE_LIST:
        analyzer = MythrilAnalyzer(
            strategy=args.strategy,
            disassembler=disassembler,
            address=address,
            max_depth=args.max_depth,
            execution_timeout=args.execution_timeout,
            loop_bound=args.loop_bound,
            create_timeout=args.create_timeout,
            enable_iprof=args.enable_iprof,
            disable_dependency_pruning=args.disable_dependency_pruning,
            use_onchain_data=not args.no_onchain_data,
            solver_timeout=args.solver_timeout,
            parallel_solving=args.parallel_solving,
            custom_modules_directory=args.custom_modules_directory
            if args.custom_modules_directory
            else "",
            call_depth_limit=args.call_depth_limit,
            sparse_pruning=args.sparse_pruning,
            unconstrained_storage=args.unconstrained_storage,
            solver_log=args.solver_log,
        )

        if not disassembler.contracts:
            exit_with_error(
                args.outform, "input files do not contain any valid contracts"
            )

        if args.attacker_address:
            try:
                ACTORS["ATTACKER"] = args.attacker_address
            except ValueError:
                exit_with_error(args.outform, "Attacker address is invalid")

        if args.creator_address:
            try:
                ACTORS["CREATOR"] = args.creator_address
            except ValueError:
                exit_with_error(args.outform, "Creator address is invalid")

        if args.graph:
            html = analyzer.graph_html(
                contract=analyzer.contracts[0],
                enable_physics=args.enable_physics,
                phrackify=args.phrack,
                transaction_count=args.transaction_count,
            )

            try:
                with open(args.graph, "w") as f:
                    f.write(html)
            except Exception as e:
                exit_with_error(args.outform, "Error saving graph: " + str(e))

        elif args.statespace_json:

            if not analyzer.contracts:
                exit_with_error(
                    args.outform, "input files do not contain any valid contracts"
                )

            statespace = analyzer.dump_statespace(contract=analyzer.contracts[0])

            try:
                with open(args.statespace_json, "w") as f:
                    json.dump(statespace, f)
            except Exception as e:
                exit_with_error(args.outform, "Error saving json: " + str(e))

        else:
            try:
                report = analyzer.fire_lasers(
                    modules=[m.strip() for m in args.modules.strip().split(",")]
                    if args.modules
                    else None,
                    transaction_count=args.transaction_count,
                )
                outputs = {
                    "json": report.as_json(),
                    "jsonv2": report.as_swc_standard_format(),
                    "text": report.as_text(),
                    "markdown": report.as_markdown(),
                }
                print(outputs[args.outform])
            except DetectorNotFoundError as e:
                exit_with_error(args.outform, format(e))
            except CriticalError as e:
                exit_with_error(
                    args.outform, "Analysis error encountered: " + format(e)
                )

    else:
        parser.print_help()


def contract_hash_to_address(args: Namespace):
    """
    prints the hash from function signature
    :param args:
    :return:
    """
    print(MythrilDisassembler.hash_for_function_signature(args.func_name))
    sys.exit()


def parse_args_and_execute(parser: ArgumentParser, args: Namespace) -> None:
    """
    Parses the arguments
    :param parser: The parser
    :param args: The args
    """

    if args.epic:
        path = os.path.dirname(os.path.realpath(__file__))
        sys.argv.remove("--epic")
        os.system(" ".join(sys.argv) + " | python3 " + path + "/epic.py")
        sys.exit()

    if args.command not in COMMAND_LIST or args.command is None:
        parser.print_help()
        sys.exit()

    if args.command == VERSION_COMMAND:
        if args.outform == "json":
            print(json.dumps({"version_str": VERSION}))
        else:
            print("Mythril version {}".format(VERSION))
        sys.exit()

    if args.command == LIST_DETECTORS_COMMAND:
        modules = []
        for module in ModuleLoader().get_detection_modules():
            modules.append({"classname": type(module).__name__, "title": module.name})
        if args.outform == "json":
            print(json.dumps(modules))
        else:
            for module_data in modules:
                print("{}: {}".format(module_data["classname"], module_data["title"]))
        sys.exit()

    if args.command == HELP_COMMAND:
        parser.print_help()
        sys.exit()

    # Parse cmdline args
    validate_args(args)
    try:
        if args.command == FUNCTION_TO_HASH_COMMAND:
            contract_hash_to_address(args)
        config = set_config(args)
        query_signature = args.__dict__.get("query_signature", None)
        solc_json = args.__dict__.get("solc_json", None)
        solv = args.__dict__.get("solv", None)
        disassembler = MythrilDisassembler(
            eth=config.eth,
            solc_version=solv,
            solc_settings_json=solc_json,
            enable_online_lookup=query_signature,
        )

        address = load_code(disassembler, args)
        execute_command(
            disassembler=disassembler, address=address, parser=parser, args=args
        )
    except CriticalError as ce:
        exit_with_error(args.__dict__.get("outform", "text"), str(ce))
    except Exception:
        exit_with_error(args.__dict__.get("outform", "text"), traceback.format_exc())


if __name__ == "__main__":
    main()
