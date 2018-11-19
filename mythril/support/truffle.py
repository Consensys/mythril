import os
from pathlib import PurePath
import re
import sys
import json
import logging
from ethereum.utils import sha3
from mythril.ether.ethcontract import ETHContract
from mythril.ether.soliditycontract import SourceMapping
from mythril.exceptions import CriticalError
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.report import Report

from mythril.ether import util
from mythril.laser.ethereum.util import get_instruction_index


def analyze_truffle_project(sigs, args):

    project_root = os.getcwd()

    build_dir = os.path.join(project_root, "build", "contracts")

    files = os.listdir(build_dir)

    for filename in files:

        if re.match(r".*\.json$", filename) and filename != "Migrations.json":

            with open(os.path.join(build_dir, filename)) as cf:
                contractdata = json.load(cf)

            try:
                name = contractdata["contractName"]
                bytecode = contractdata["deployedBytecode"]
                filename = PurePath(contractdata["sourcePath"]).name
            except KeyError:
                print(
                    "Unable to parse contract data. Please use Truffle 4 to compile your project."
                )
                sys.exit()
            if len(bytecode) < 4:
                continue
            get_sigs_from_truffle(sigs, contractdata)

            ethcontract = ETHContract(bytecode, name=name)

            address = util.get_indexed_address(0)
            sym = SymExecWrapper(
                ethcontract,
                address,
                args.strategy,
                max_depth=args.max_depth,
                create_timeout=args.create_timeout,
                execution_timeout=args.execution_timeout,
                transaction_count=args.transaction_count,
            )
            issues = fire_lasers(sym)

            if not len(issues):
                if args.outform == "text" or args.outform == "markdown":
                    print("# Analysis result for " + name + "\n\nNo issues found.")
                else:
                    result = {
                        "contract": name,
                        "result": {"success": True, "error": None, "issues": []},
                    }
                    print(json.dumps(result))
            else:

                report = Report()
                # augment with source code

                deployed_disassembly = ethcontract.disassembly
                constructor_disassembly = ethcontract.creation_disassembly

                source = contractdata["source"]

                deployed_source_map = contractdata["deployedSourceMap"].split(";")
                source_map = contractdata["sourceMap"].split(";")

                deployed_mappings = get_mappings(source, deployed_source_map)
                constructor_mappings = get_mappings(source, source_map)

                for issue in issues:
                    if issue.function == "constructor":
                        mappings = constructor_mappings
                        disassembly = constructor_disassembly
                    else:
                        mappings = deployed_mappings
                        disassembly = deployed_disassembly

                    index = get_instruction_index(
                        disassembly.instruction_list, issue.address
                    )

                    if index:
                        try:
                            offset = mappings[index].offset
                            length = mappings[index].length

                            issue.filename = filename
                            issue.code = source.encode("utf-8")[
                                offset : offset + length
                            ].decode("utf-8")
                            issue.lineno = mappings[index].lineno
                        except IndexError:
                            logging.debug("No code mapping at index %d", index)

                    report.append_issue(issue)

                if args.outform == "json":

                    result = {
                        "contract": name,
                        "result": {
                            "success": True,
                            "error": None,
                            "issues": list(map(lambda x: x.as_dict, issues)),
                        },
                    }
                    print(json.dumps(result))

                else:
                    if args.outform == "text":
                        print(
                            "# Analysis result for " + name + ":\n\n" + report.as_text()
                        )
                    elif args.outform == "markdown":
                        print(report.as_markdown())


def get_sigs_from_truffle(sigs, contract_data):
    abis = contract_data["abi"]
    for abi in abis:
        if abi["type"] != "function":
            continue
        function_name = abi["name"]
        list_of_args = ",".join([input["type"] for input in abi["inputs"]])
        signature = function_name + "(" + list_of_args + ")"
        sigs.add("0x" + sha3(signature)[:4].hex(), signature)


def get_mappings(source, deployed_source_map):
    mappings = []
    for item in deployed_source_map:
        mapping = item.split(":")

        if len(mapping) > 0 and len(mapping[0]) > 0:
            offset = int(mapping[0])

        if len(mapping) > 1 and len(mapping[1]) > 0:
            length = int(mapping[1])

        if len(mapping) > 2 and len(mapping[2]) > 0:
            idx = int(mapping[2])

        lineno = source.encode("utf-8")[0:offset].count("\n".encode("utf-8")) + 1

        mappings.append(SourceMapping(idx, offset, length, lineno))

    return mappings
