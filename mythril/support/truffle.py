import os
import re
import sys
import json
from mythril.ether.ethcontract import ETHContract
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import StateSpace
from mythril.analysis.report import Report
from laser.ethereum import helper


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
            except:
                print("Unable to parse contract data. Please use Truffle 4 to compile your project.")
                sys.exit()

            if (len(bytecode) < 4):
                continue

            ethcontract = ETHContract(bytecode, name=name)

            states = StateSpace([ethcontract], max_depth=10)
            issues = fire_lasers(states)

            if not len(issues):
                if (args.outform == 'text' or args.outform == 'markdown'):
                    print("Analysis result for " + name + ": No issues found.")
                else:
                    result = {'contract': name, 'result': {'success': True, 'error': None, 'issues': []}}
                    print(json.dumps(result))
            else:

                report = Report()
                # augment with source code

                disassembly = ethcontract.get_disassembly()
                source = contractdata['source']

                deployedSourceMap = contractdata['deployedSourceMap'].split(";")

                mappings = []
                i = 0

                for item in deployedSourceMap:

                    mapping = item.split(":")

                    if len(mapping) > 0 and len(mapping[0]) > 0:
                        offset = int(mapping[0])

                    if len(mapping) > 1 and len(mapping[1]) > 0:
                        length = int(mapping[1])

                    mappings.append((int(offset), int(length)))

                for issue in issues:

                    index = helper.get_instruction_index(disassembly.instruction_list, issue.pc)

                    if index:
                        issue.code_start = mappings[index][0]
                        issue.code_length = mappings[index][1]
                        issue.code = source[mappings[index][0]: mappings[index][0] + mappings[index][1]]

                    report.append_issue(issue)

                if (args.outform == 'json'):

                    result = {'contract': name, 'result': {'success': True, 'error': None, 'issues': list(map(lambda x: x.as_dict(), issues))}}
                    print(json.dumps(result))

                else:

                    if (args.outform == 'text'):
                        print("Analysis result for " + name + ":\n" + report.as_text())
                    elif (args.outform == 'markdown'):
                        print("Analysis result for " + name + ":\n" + report.as_markdown())
