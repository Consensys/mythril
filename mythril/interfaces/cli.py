#!/usr/bin/env python3
# -*- coding: UTF-8 -*-
"""mythril.py: Bug hunting on the Ethereum blockchain

   http://www.github.com/ConsenSys/mythril
"""

import logging
import json
import sys
import argparse

# logging.basicConfig(level=logging.DEBUG)

from mythril.exceptions import CriticalError
from mythril.mythril import Mythril


def exit_with_error(format, message):
    if format == 'text' or format == 'markdown':
        print(message)
    else:
        result = {'success': False, 'error': str(message), 'issues': []}
        print(json.dumps(result))
    sys.exit()


def main():
    parser = argparse.ArgumentParser(description='Security analysis of Ethereum smart contracts')
    parser.add_argument("solidity_file", nargs='*')

    commands = parser.add_argument_group('commands')
    commands.add_argument('-g', '--graph', help='generate a control flow graph')
    commands.add_argument('-x', '--fire-lasers', action='store_true',
                          help='detect vulnerabilities, use with -c, -a or solidity file(s)')
    commands.add_argument('-t', '--truffle', action='store_true',
                          help='analyze a truffle project (run from project dir)')
    commands.add_argument('-d', '--disassemble', action='store_true', help='print disassembly')
    commands.add_argument('-j', '--statespace-json', help='dumps the statespace json', metavar='OUTPUT_FILE')

    inputs = parser.add_argument_group('input arguments')
    inputs.add_argument('-c', '--code', help='hex-encoded bytecode string ("6060604052...")', metavar='BYTECODE')
    inputs.add_argument('-a', '--address', help='pull contract from the blockchain', metavar='CONTRACT_ADDRESS')
    inputs.add_argument('-l', '--dynld', action='store_true', help='auto-load dependencies from the blockchain')

    outputs = parser.add_argument_group('output formats')
    outputs.add_argument('-o', '--outform', choices=['text', 'markdown', 'json'], default='text',
                         help='report output format', metavar='<text/json>')
    outputs.add_argument('--verbose-report', action='store_true', help='Include debugging information in report')

    database = parser.add_argument_group('local contracts database')
    database.add_argument('--init-db', action='store_true', help='initialize the contract database')
    database.add_argument('-s', '--search', help='search the contract database', metavar='EXPRESSION')

    utilities = parser.add_argument_group('utilities')
    utilities.add_argument('--hash', help='calculate function signature hash', metavar='SIGNATURE')
    utilities.add_argument('--storage', help='read state variables from storage index, use with -a',
                           metavar='INDEX,NUM_SLOTS,[array] / mapping,INDEX,[KEY1, KEY2...]')
    utilities.add_argument('--solv',
                           help='specify solidity compiler version. If not present, will try to install it (Experimental)',
                           metavar='SOLV')

    options = parser.add_argument_group('options')
    options.add_argument('-m', '--modules', help='Comma-separated list of security analysis modules', metavar='MODULES')
    options.add_argument('--max-depth', type=int, default=22, help='Maximum recursion depth for symbolic execution')
    options.add_argument('--solc-args', help='Extra arguments for solc')
    options.add_argument('--phrack', action='store_true', help='Phrack-style call graph')
    options.add_argument('--enable-physics', action='store_true', help='enable graph physics simulation')
    options.add_argument('-v', type=int, help='log level (0-2)', metavar='LOG_LEVEL')
    options.add_argument('--leveldb', help='enable direct leveldb access operations', metavar='LEVELDB_PATH')

    rpc = parser.add_argument_group('RPC options')
    rpc.add_argument('-i', action='store_true', help='Preset: Infura Node service (Mainnet)')
    rpc.add_argument('--rpc', help='custom RPC settings', metavar='HOST:PORT / ganache / infura-[network_name]')
    rpc.add_argument('--rpctls', type=bool, default=False, help='RPC connection over TLS')
    rpc.add_argument('--ipc', action='store_true', help='Connect via local IPC')

    # Get config values

    args = parser.parse_args()

    # -- args sanity checks --
    # Detect unsupported combinations of command line args

    if args.dynld and not args.address:
        exit_with_error(args.outform, "Dynamic loader can be used in on-chain analysis mode only (-a).")

    # Parse cmdline args

    if not (args.search or args.init_db or args.hash or args.disassemble or args.graph or args.fire_lasers
            or args.storage or args.truffle or args.statespace_json):
        parser.print_help()
        sys.exit()

    if args.v:
        if 0 <= args.v < 3:
            logging.basicConfig(level=[logging.NOTSET, logging.INFO, logging.DEBUG][args.v])
        else:
            exit_with_error(args.outform, "Invalid -v value, you can find valid values in usage")

    # -- commands --
    if args.hash:
        print(Mythril.hash_for_function_signature(args.hash))
        sys.exit()


    try:
        # the mythril object should be our main interface
        #init_db = None, infura = None, rpc = None, rpctls = None, ipc = None,
        #solc_args = None, dynld = None, max_recursion_depth = 12):


        mythril = Mythril(solv=args.solv, dynld=args.dynld,
                          solc_args=args.solc_args)

        if args.leveldb:
            # Open LevelDB if specified
            mythril.set_db_leveldb(args.leveldb)

        elif (args.address or args.init_db) and not args.leveldb:
            # Establish RPC/IPC connection if necessary
            if args.i:
                mythril.set_db_rpc_infura()
            elif args.rpc:
                mythril.set_db_rpc(rpc=args.rpc, rpctls=args.rpctls)
            elif args.ipc:
                mythril.set_db_ipc()
            else:
                mythril.set_db_rpc_localhost()

        if args.truffle:
            try:
                # not really pythonic atm. needs refactoring
                mythril.analyze_truffle_project(args)
            except FileNotFoundError:
                print(
                    "Build directory not found. Make sure that you start the analysis from the project root, and that 'truffle compile' has executed successfully.")
            sys.exit()

        elif args.search:
            # Database search ops
            mythril.search_db(args.search)
            sys.exit()

        elif args.init_db:
            mythril.init_db()
            sys.exit()

        # Load / compile input contracts
        address = None

        if args.code:
            # Load from bytecode
            address, _ = mythril.load_from_bytecode(args.code)
        elif args.address:
            # Get bytecode from a contract address
            address, _ = mythril.load_from_address(args.address)
        elif args.solidity_file:
            # Compile Solidity source file(s)
            #if args.graph and len(args.solidity_file) > 1:
            #    exit_with_error(args.outform,
            #                    "Cannot generate call graphs from multiple input files. Please do it one at a time.")
            address, _ = mythril.load_from_solidity(args.solidity_file)  # list of files
        else:
            exit_with_error(args.outform,
                            "No input bytecode. Please provide EVM code via -c BYTECODE, -a ADDRESS, or -i SOLIDITY_FILES")

        # Commands

        if args.storage:
            if not args.address:
                exit_with_error(args.outform,
                                "To read storage, provide the address of a deployed contract with the -a option.")

            storage = mythril.get_state_variable_from_storage(address=address,
                                                              params=[a.strip() for a in args.storage.strip().split(",")])
            print(storage)

        elif args.disassemble:
            easm_text = mythril.contracts[0].get_easm() # or mythril.disassemble(mythril.contracts[0])
            sys.stdout.write(easm_text)

        elif args.graph or args.fire_lasers:
            if not mythril.contracts:
                exit_with_error(args.outform, "input files do not contain any valid contracts")

            if args.graph:
                html = mythril.graph_html(mythril.contracts[0], address=address,
                                          enable_physics=args.enable_physics, phrackify=args.phrack,
                                          max_depth=args.max_depth)

                try:
                    with open(args.graph, "w") as f:
                        f.write(html)
                except Exception as e:
                    exit_with_error(args.outform, "Error saving graph: " + str(e))

            else:
                report = mythril.fire_lasers(address=address,
                                             modules=[m.strip() for m in args.modules.strip().split(",")] if args.modules else [],
                                             verbose_report=args.verbose_report,
                                             max_depth=args.max_depth)
                outputs = {
                    'json': report.as_json(),
                    'text': report.as_text(),
                    'markdown': report.as_markdown()
                }
                print(outputs[args.outform])

        elif args.statespace_json:

            if not mythril.contracts:
                exit_with_error(args.outform, "input files do not contain any valid contracts")

            statespace = mythril.dump_statespace(mythril.contracts[0], address=address, max_depth=args.max_depth)

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
