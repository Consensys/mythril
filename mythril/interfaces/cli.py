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

import mythril.support.signatures as sigs
from mythril.exceptions import AddressNotFoundError, CriticalError
from mythril.mythril import Mythril
from mythril.version import VERSION

# logging.basicConfig(level=logging.DEBUG)

log = logging.getLogger(__name__)


def exit_with_error(format_, message):
    """

    :param format_:
    :param message:
    """
    if format_ == "text" or format_ == "markdown":
        log.error(message)
    else:
        result = {"success": False, "error": str(message), "issues": []}
        print(json.dumps(result))
    sys.exit()


def main():
    """The main CLI interface entry point."""
    parser = argparse.ArgumentParser(
        description="Security analysis of Ethereum smart contracts"
    )
    parser.add_argument("solidity_file", nargs="*")

    commands = parser.add_argument_group("commands")
    commands.add_argument("-g", "--graph", help="generate a control flow graph")
    commands.add_argument(
        "-V",
        "--version",
        action="store_true",
        help="print the Mythril version number and exit",
    )
    commands.add_argument(
        "-x",
        "--fire-lasers",
        action="store_true",
        help="detect vulnerabilities, use with -c, -a or solidity file(s)",
    )
    commands.add_argument(
        "--truffle",
        action="store_true",
        help="analyze a truffle project (run from project dir)",
    )
    commands.add_argument(
        "-d", "--disassemble", action="store_true", help="print disassembly"
    )
    commands.add_argument(
        "-j",
        "--statespace-json",
        help="dumps the statespace json",
        metavar="OUTPUT_FILE",
    )

    inputs = parser.add_argument_group("input arguments")
    inputs.add_argument(
        "-c",
        "--code",
        help='hex-encoded bytecode string ("6060604052...")',
        metavar="BYTECODE",
    )
    inputs.add_argument(
        "-f",
        "--codefile",
        help="file containing hex-encoded bytecode string",
        metavar="BYTECODEFILE",
        type=argparse.FileType("r"),
    )
    inputs.add_argument(
        "-a",
        "--address",
        help="pull contract from the blockchain",
        metavar="CONTRACT_ADDRESS",
    )
    inputs.add_argument(
        "-l",
        "--dynld",
        action="store_true",
        help="auto-load dependencies from the blockchain",
    )
    inputs.add_argument(
        "--no-onchain-storage-access",
        action="store_true",
        help="turns off getting the data from onchain contracts",
    )
    inputs.add_argument(
        "--bin-runtime",
        action="store_true",
        help="Only when -c or -f is used. Consider the input bytecode as binary runtime code, default being the contract creation bytecode.",
    )

    outputs = parser.add_argument_group("output formats")
    outputs.add_argument(
        "-o",
        "--outform",
        choices=["text", "markdown", "json", "jsonv2"],
        default="text",
        help="report output format",
        metavar="<text/markdown/json/jsonv2>",
    )
    outputs.add_argument(
        "--verbose-report",
        action="store_true",
        help="Include debugging information in report",
    )

    database = parser.add_argument_group("local contracts database")
    database.add_argument(
        "-s", "--search", help="search the contract database", metavar="EXPRESSION"
    )
    database.add_argument(
        "--leveldb-dir",
        help="specify leveldb directory for search or direct access operations",
        metavar="LEVELDB_PATH",
    )

    utilities = parser.add_argument_group("utilities")
    utilities.add_argument(
        "--hash", help="calculate function signature hash", metavar="SIGNATURE"
    )
    utilities.add_argument(
        "--storage",
        help="read state variables from storage index, use with -a",
        metavar="INDEX,NUM_SLOTS,[array] / mapping,INDEX,[KEY1, KEY2...]",
    )
    utilities.add_argument(
        "--solv",
        help="specify solidity compiler version. If not present, will try to install it (Experimental)",
        metavar="SOLV",
    )
    utilities.add_argument(
        "--contract-hash-to-address",
        help="returns corresponding address for a contract address hash",
        metavar="SHA3_TO_LOOK_FOR",
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
        default=22,
        help="Maximum recursion depth for symbolic execution",
    )

    options.add_argument(
        "--strategy",
        choices=["dfs", "bfs", "naive-random", "weighted-random"],
        default="dfs",
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
    options.add_argument("--solc-args", help="Extra arguments for solc")
    options.add_argument(
        "--phrack", action="store_true", help="Phrack-style call graph"
    )
    options.add_argument(
        "--enable-physics", action="store_true", help="enable graph physics simulation"
    )
    options.add_argument(
        "-v", type=int, help="log level (0-5)", metavar="LOG_LEVEL", default=2
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

    rpc = parser.add_argument_group("RPC options")

    rpc.add_argument(
        "--rpc",
        help="custom RPC settings",
        metavar="HOST:PORT / ganache / infura-[network_name]",
        default="infura-mainnet",
    )
    rpc.add_argument(
        "--rpctls", type=bool, default=False, help="RPC connection over TLS"
    )
    parser.add_argument("--epic", action="store_true", help=argparse.SUPPRESS)

    # Get config values

    args = parser.parse_args()

    if args.epic:
        path = os.path.dirname(os.path.realpath(__file__))
        sys.argv.remove("--epic")
        os.system(" ".join(sys.argv) + " | python3 " + path + "/epic.py")
        sys.exit()

    if args.version:
        if args.outform == "json":
            print(json.dumps({"version_str": VERSION}))
        else:
            print("Mythril version {}".format(VERSION))
        sys.exit()

    # Parse cmdline args

    if not (
        args.search
        or args.hash
        or args.disassemble
        or args.graph
        or args.fire_lasers
        or args.storage
        or args.truffle
        or args.statespace_json
        or args.contract_hash_to_address
    ):
        parser.print_help()
        sys.exit()

    if args.v:
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

    if args.query_signature:
        if sigs.ethereum_input_decoder == None:
            exit_with_error(
                args.outform,
                "The --query-signature function requires the python package ethereum-input-decoder",
            )

    if args.enable_iprof:
        if args.v < 4:
            exit_with_error(
                args.outform,
                "--enable-iprof must be used with -v LOG_LEVEL where LOG_LEVEL >= 4",
            )
        elif not (args.graph or args.fire_lasers or args.statespace_json):
            exit_with_error(
                args.outform,
                "--enable-iprof must be used with one of -g, --graph, -x, --fire-lasers, -j and --statespace-json",
            )

    # -- commands --
    if args.hash:
        print(Mythril.hash_for_function_signature(args.hash))
        sys.exit()

    try:
        # the mythril object should be our main interface
        # infura = None, rpc = None, rpctls = None
        # solc_args = None, dynld = None, max_recursion_depth = 12):

        mythril = Mythril(
            solv=args.solv,
            dynld=args.dynld,
            onchain_storage_access=(not args.no_onchain_storage_access),
            solc_args=args.solc_args,
            enable_online_lookup=args.query_signature,
        )
        if (
            args.dynld
            or not args.no_onchain_storage_access
            and not (args.rpc or args.i)
        ):
            mythril.set_api_from_config_path()

        if args.address:
            # Establish RPC connection if necessary
            mythril.set_api_rpc(rpc=args.rpc, rpctls=args.rpctls)
        elif args.search or args.contract_hash_to_address:
            # Open LevelDB if necessary
            mythril.set_api_leveldb(
                mythril.leveldb_dir if not args.leveldb_dir else args.leveldb_dir
            )

        if args.search:
            # Database search ops
            mythril.search_db(args.search)
            sys.exit()

        if args.contract_hash_to_address:
            # search corresponding address
            try:
                mythril.contract_hash_to_address(args.contract_hash_to_address)
            except AddressNotFoundError:
                print("Address not found.")

            sys.exit()

        if args.truffle:
            try:
                # not really pythonic atm. needs refactoring
                mythril.analyze_truffle_project(args)
            except FileNotFoundError:
                print(
                    "Build directory not found. Make sure that you start the analysis from the project root, and that 'truffle compile' has executed successfully."
                )
            sys.exit()

        # Load / compile input contracts
        address = None

        if args.code:
            # Load from bytecode
            code = args.code[2:] if args.code.startswith("0x") else args.code
            address, _ = mythril.load_from_bytecode(code, args.bin_runtime)
        elif args.codefile:
            bytecode = "".join([l.strip() for l in args.codefile if len(l.strip()) > 0])
            bytecode = bytecode[2:] if bytecode.startswith("0x") else bytecode
            address, _ = mythril.load_from_bytecode(bytecode, args.bin_runtime)
        elif args.address:
            # Get bytecode from a contract address
            address, _ = mythril.load_from_address(args.address)
        elif args.solidity_file:
            # Compile Solidity source file(s)
            if args.graph and len(args.solidity_file) > 1:
                exit_with_error(
                    args.outform,
                    "Cannot generate call graphs from multiple input files. Please do it one at a time.",
                )
            address, _ = mythril.load_from_solidity(args.solidity_file)  # list of files
        else:
            exit_with_error(
                args.outform,
                "No input bytecode. Please provide EVM code via -c BYTECODE, -a ADDRESS, or -i SOLIDITY_FILES",
            )

        # Commands

        if args.storage:
            if not args.address:
                exit_with_error(
                    args.outform,
                    "To read storage, provide the address of a deployed contract with the -a option.",
                )

            storage = mythril.get_state_variable_from_storage(
                address=address,
                params=[a.strip() for a in args.storage.strip().split(",")],
            )
            print(storage)

        elif args.disassemble:
            # or mythril.disassemble(mythril.contracts[0])

            if mythril.contracts[0].code:
                print("Runtime Disassembly: \n" + mythril.contracts[0].get_easm())
            if mythril.contracts[0].creation_code:
                print("Disassembly: \n" + mythril.contracts[0].get_creation_easm())

        elif args.graph or args.fire_lasers:
            if not mythril.contracts:
                exit_with_error(
                    args.outform, "input files do not contain any valid contracts"
                )

            if args.graph:
                html = mythril.graph_html(
                    strategy=args.strategy,
                    contract=mythril.contracts[0],
                    address=address,
                    enable_physics=args.enable_physics,
                    phrackify=args.phrack,
                    max_depth=args.max_depth,
                    execution_timeout=args.execution_timeout,
                    create_timeout=args.create_timeout,
                    enable_iprof=args.enable_iprof,
                )

                try:
                    with open(args.graph, "w") as f:
                        f.write(html)
                except Exception as e:
                    exit_with_error(args.outform, "Error saving graph: " + str(e))

            else:
                try:
                    report = mythril.fire_lasers(
                        strategy=args.strategy,
                        address=address,
                        modules=[m.strip() for m in args.modules.strip().split(",")]
                        if args.modules
                        else [],
                        verbose_report=args.verbose_report,
                        max_depth=args.max_depth,
                        execution_timeout=args.execution_timeout,
                        create_timeout=args.create_timeout,
                        transaction_count=args.transaction_count,
                        enable_iprof=args.enable_iprof,
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

        elif args.statespace_json:

            if not mythril.contracts:
                exit_with_error(
                    args.outform, "input files do not contain any valid contracts"
                )

            statespace = mythril.dump_statespace(
                strategy=args.strategy,
                contract=mythril.contracts[0],
                address=address,
                max_depth=args.max_depth,
                execution_timeout=args.execution_timeout,
                create_timeout=args.create_timeout,
                enable_iprof=args.enable_iprof,
            )

            try:
                with open(args.statespace_json, "w") as f:
                    json.dump(statespace, f)
            except Exception as e:
                exit_with_error(args.outform, "Error saving json: " + str(e))

        else:
            parser.print_help()

    except CriticalError as ce:
        exit_with_error(args.outform, str(ce))


if __name__ == "__main__":
    main()
