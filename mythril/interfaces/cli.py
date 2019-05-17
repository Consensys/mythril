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
from argparse import ArgumentParser, Namespace
from mythril.exceptions import AddressNotFoundError, CriticalError
from mythril.mythril import (
    MythrilAnalyzer,
    MythrilDisassembler,
    MythrilConfig,
    MythrilLevelDB,
)
from mythril.version import VERSION

# logging.basicConfig(level=logging.DEBUG)

log = logging.getLogger(__name__)


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
                "meta": {
                    "logs": [{"level": "error", "hidden": "true", "msg": message}]
                },
            }
        ]
        print(json.dumps(result))
    sys.exit()


def get_input_parser() -> ArgumentParser:
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


def get_output_parser() -> ArgumentParser:
    """
    Get parser which handles output
    :return: Parser which handles output
    """
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--epic", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument(
        "-o",
        "--outform",
        choices=["text", "markdown", "json", "jsonv2"],
        default="text",
        help="report output format",
        metavar="<text/markdown/json/jsonv2>",
    )
    parser.add_argument(
        "--verbose-report",
        action="store_true",
        help="Include debugging information in report",
    )
    parser.add_argument(
        "-v", type=int, help="log level (0-5)", metavar="LOG_LEVEL", default=2
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
    return parser


def get_utilities_parser() -> ArgumentParser:
    """
    Get parser which handles utilities flags
    :return: Parser which handles utility flags
    """
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("--solc-args", help="Extra arguments for solc")
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
    input_parser = get_input_parser()
    output_parser = get_output_parser()
    parser = argparse.ArgumentParser(
        description="Security analysis of Ethereum smart contracts"
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")
    analyzer_parser = subparsers.add_parser(
        "analyze",
        help="Triggers the analysis of the smart contract",
        parents=[rpc_parser, utilities_parser, input_parser, output_parser],
    )
    disassemble_parser = subparsers.add_parser(
        "disassemble",
        help="Disassembles the smart contract",
        parents=[rpc_parser, utilities_parser, input_parser, output_parser],
    )
    read_storage_parser = subparsers.add_parser(
        "read-storage",
        help="Retrieves storage slots from a given address through rpc",
        parents=[rpc_parser, output_parser],
    )
    leveldb_search_parser = subparsers.add_parser(
        "leveldb-search",
        parents=[output_parser],
        help="Searches the code fragment in local leveldb",
    )
    contract_func_to_hash = subparsers.add_parser(
        "function-to-hash",
        parents=[output_parser],
        help="Returns the hash signature of the function",
    )
    contract_hash_to_addr = subparsers.add_parser(
        "hash-to-address",
        parents=[output_parser],
        help="converts the hashes in the blockchain to ethereum address",
    )
    subparsers.add_parser(
        "version", parents=[output_parser], help="Outputs the version"
    )

    create_disassemble_parser(disassemble_parser)
    create_analyzer_parser(analyzer_parser)
    create_read_storage_parser(read_storage_parser)
    create_hash_to_addr_parser(contract_hash_to_addr)
    create_func_to_hash_parser(contract_func_to_hash)
    create_leveldb_parser(leveldb_search_parser)

    subparsers.add_parser("truffle", parents=[analyzer_parser], add_help=False)

    # Get config values

    args = parser.parse_args()
    parse_args(parser=parser, args=args)


def create_disassemble_parser(parser: ArgumentParser):
    """
    Modify parser to handle disassembly
    :param parser:
    :return:
    """
    parser.add_argument("solidity_file", nargs="*")


def create_read_storage_parser(read_storage_parser: ArgumentParser):
    """
    Modify parser to handle storage slots
    :param read_storage_parser:
    :return:
    """

    read_storage_parser.add_argument(
        "storage_slots",
        help="read state variables from storage index, use with -a",
        metavar="INDEX,NUM_SLOTS,[array] / mapping,INDEX,[KEY1, KEY2...]",
    )
    read_storage_parser.add_argument(
        "address", help="contract address", metavar="ADDRESS"
    )


def create_leveldb_parser(parser: ArgumentParser):
    """
    Modify parser to handle leveldb-search
    :param parser:
    :return:
    """
    parser.add_argument("search")
    parser.add_argument(
        "--leveldb-dir",
        help="specify leveldb directory for search or direct access operations",
        metavar="LEVELDB_PATH",
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
    hash_parser.add_argument(
        "--leveldb-dir",
        help="specify leveldb directory for search or direct access operations",
        metavar="LEVELDB_PATH",
    )


def create_analyzer_parser(analyzer_parser: ArgumentParser):
    """
    Modify parser to handle analyze command
    :param analyzer_parser:
    :return:
    """
    analyzer_parser.add_argument("solidity_file", nargs="*")
    commands = analyzer_parser.add_argument_group("commands")
    commands.add_argument("-g", "--graph", help="generate a control flow graph")
    commands.add_argument(
        "-j",
        "--statespace-json",
        help="dumps the statespace json",
        metavar="OUTPUT_FILE",
    )
    commands.add_argument(
        "--truffle",
        action="store_true",
        help="analyze a truffle project (run from project dir)",
    )
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
        default=50,
        help="Maximum recursion depth for symbolic execution",
    )

    options.add_argument(
        "--strategy",
        choices=["dfs", "bfs", "naive-random", "weighted-random"],
        default="bfs",
        help="Symbolic execution strategy",
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
        default=600,
        help="The amount of seconds to spend on symbolic execution",
    )
    options.add_argument(
        "--create-timeout",
        type=int,
        default=10,
        help="The amount of seconds to spend on " "the initial contract creation",
    )
    options.add_argument(
        "-l",
        "--dynld",
        action="store_true",
        help="auto-load dependencies from the blockchain",
    )
    options.add_argument(
        "--no-onchain-storage-access",
        action="store_true",
        help="turns off getting the data from onchain contracts",
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

    if args.command == "analyze":
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
    if (
        args.command == "analyze" and (args.dynld or not args.no_onchain_storage_access)
    ) and not (args.rpc or args.i):
        config.set_api_from_config_path()

    if args.__dict__.get("address", None):
        # Establish RPC connection if necessary
        config.set_api_rpc(rpc=args.rpc, rpctls=args.rpctls)
    if args.command in ("hash-to-address", "leveldb-search"):
        # Open LevelDB if necessary
        if not args.__dict__.get("leveldb_dir", None):
            leveldb_dir = config.leveldb_dir
        else:
            leveldb_dir = args.leveldb_dir
        config.set_api_leveldb(leveldb_dir)
    return config


def leveldb_search(config: MythrilConfig, args: Namespace):
    """
    Handle leveldb search
    :param config:
    :param args:
    :return:
    """
    if args.command in ("hash-to-address", "leveldb-search"):
        leveldb_searcher = MythrilLevelDB(config.eth_db)
        if args.command == "leveldb-search":
            # Database search ops
            leveldb_searcher.search_db(args.search)

        else:
            # search corresponding address
            try:
                leveldb_searcher.contract_hash_to_address(args.hash)
            except AddressNotFoundError:
                print("Address not found.")

        sys.exit()


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
    elif args.__dict__.get("solidity_file", False):
        # Compile Solidity source file(s)
        if args.command == "analyze" and args.graph and len(args.solidity_file) > 1:
            exit_with_error(
                args.outform,
                "Cannot generate call graphs from multiple input files. Please do it one at a time.",
            )
        address, _ = disassembler.load_from_solidity(
            args.solidity_file
        )  # list of files
    else:
        exit_with_error(
            args.outform,
            "No input bytecode. Please provide EVM code via -c BYTECODE, -a ADDRESS, or -i SOLIDITY_FILES",
        )
    return address


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
        return

    if args.command == "disassemble":
        # or mythril.disassemble(mythril.contracts[0])

        if disassembler.contracts[0].code:
            print("Runtime Disassembly: \n" + disassembler.contracts[0].get_easm())
        if disassembler.contracts[0].creation_code:
            print("Disassembly: \n" + disassembler.contracts[0].get_creation_easm())

    elif args.command == "analyze":
        analyzer = MythrilAnalyzer(
            strategy=args.strategy,
            disassembler=disassembler,
            address=address,
            max_depth=args.max_depth,
            execution_timeout=args.execution_timeout,
            create_timeout=args.create_timeout,
            enable_iprof=args.enable_iprof,
            onchain_storage_access=not args.no_onchain_storage_access,
        )

        if not disassembler.contracts:
            exit_with_error(
                args.outform, "input files do not contain any valid contracts"
            )

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
                    else [],
                    verbose_report=args.verbose_report,
                    transaction_count=args.transaction_count,
                )
                outputs = {
                    "json": report.as_json(),
                    "jsonv2": report.as_swc_standard_format(),
                    "text": report.as_text(),
                    "markdown": report.as_markdown(),
                }
                print(outputs[args.outform])
            except ModuleNotFoundError as e:
                exit_with_error(
                    args.outform, "Error loading analyis modules: " + format(e)
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


def parse_args(parser: ArgumentParser, args: Namespace) -> None:
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

    if args.command == "version":
        if args.outform == "json":
            print(json.dumps({"version_str": VERSION}))
        else:
            print("Mythril version {}".format(VERSION))
        sys.exit()

    # Parse cmdline args
    validate_args(args)
    try:
        if args.command == "function-to-hash":
            contract_hash_to_address(args)
        config = set_config(args)
        leveldb_search(config, args)
        query_signature = args.__dict__.get("query_signature", None)
        solc_args = args.__dict__.get("solc_args", None)
        solv = args.__dict__.get("solv", None)
        disassembler = MythrilDisassembler(
            eth=config.eth,
            solc_version=solv,
            solc_args=solc_args,
            enable_online_lookup=query_signature,
        )
        if args.command == "truffle":
            try:
                disassembler.analyze_truffle_project(args)
            except FileNotFoundError:
                print(
                    "Build directory not found. Make sure that you start the analysis from the project root, "
                    "and that 'truffle compile' has executed successfully."
                )
            sys.exit()

        address = load_code(disassembler, args)
        execute_command(
            disassembler=disassembler, address=address, parser=parser, args=args
        )
    except CriticalError as ce:
        exit_with_error(args.outform, str(ce))
    except Exception:
        exit_with_error(args.outform, traceback.format_exc())


if __name__ == "__main__":
    main()
