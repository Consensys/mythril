import os
import re
import sys
import json
import logging
from mythril.ether.ethcontract import ETHContract
from mythril.ether.soliditycontract import SourceMapping
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.analysis.report import Report

from mythril.ether import util
from mythril.laser.ethereum.util import get_instruction_index


def analyze_truffle_project(args):

    project_root = os.getcwd()

    build_dir = os.path.join(project_root, "build", "contracts")

    files = os.listdir(build_dir)

    for filename in files:

        if re.match(r'.*\.json$', filename) and filename != "Migrations.json":

            with open(os.path.join(build_dir, filename)) as cf:
                contractdata = json.load(cf)

            try:
                name = contractdata['contractName']
                bytecode = contractdata['deployedBytecode']
                filename = contractdata['sourcePath'].split('/')[-1]
            except:
                print("Unable to parse contract data. Please use Truffle 4 to compile your project.")
                sys.exit()

            if (len(bytecode) < 4):
                continue

            ethcontract = ETHContract(bytecode, name=name)

            address = util.get_indexed_address(0)
            sym = SymExecWrapper(ethcontract, address, args.strategy, max_depth=args.max_depth)
            issues = fire_lasers(sym)

            if not len(issues):
                if (args.outform == 'text' or args.outform == 'markdown'):
                    print("# Analysis result for " + name + "\n\nNo issues found.")
                else:
                    result = {'contract': name, 'result': {'success': True, 'error': None, 'issues': []}}
                    print(json.dumps(result))
            else:

                report = Report()
                # augment with source code

                disassembly = ethcontract.disassembly
                source = contractdata['source']

                deployedSourceMap = contractdata['deployedSourceMap'].split(";")

                mappings = []

                for item in deployedSourceMap:
                    mapping = item.split(":")

                    if len(mapping) > 0 and len(mapping[0]) > 0:
                        offset = int(mapping[0])

                    if len(mapping) > 1 and len(mapping[1]) > 0:
                        length = int(mapping[1])

                    if len(mapping) > 2 and len(mapping[2]) > 0:
                        idx = int(mapping[2])

                    lineno = source[0:offset].count('\n') + 1

                    mappings.append(SourceMapping(idx, offset, length, lineno))

                for issue in issues:

                    index = get_instruction_index(disassembly.instruction_list, issue.address)

                    if index:
                            try:
                                offset = mappings[index].offset
                                length = mappings[index].length

                                issue.filename = filename
                                issue.code = source[offset:offset + length]
                                issue.lineno = mappings[index].lineno
                            except IndexError:
                                logging.debug("No code mapping at index %d", index)

                    report.append_issue(issue)

                if (args.outform == 'json'):

                    result = {'contract': name, 'result': {'success': True, 'error': None, 'issues': list(map(lambda x: x.as_dict, issues))}}
                    print(json.dumps(result))

                else:
                    if (args.outform == 'text'):
                        print("# Analysis result for " + name + ":\n\n" + report.as_text())
                    elif (args.outform == 'markdown'):
                        print(report.as_markdown())
