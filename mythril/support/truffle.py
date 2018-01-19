import os
import re
import json
from mythril.ether import util
from mythril.ether.ethcontract import ETHContract
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import StateSpace
from laser.ethereum import helper


def analyze_truffle_project():

    project_root = os.getcwd()
    
    build_dir = os.path.join(project_root, "build", "contracts")

    contract_files = os.listdir(build_dir)

    for contract_file in contract_files:

        with open(os.path.join(build_dir, contract_file)) as cf:
            contractdata = json.load(cf)

        name = contractdata['contractName']
        bytecode = contractdata['deployedBytecode']

        if (len(bytecode) < 4):
            continue

        ethcontract= ETHContract(bytecode, name=name, address = util.get_indexed_address(0))

        contracts = [ethcontract]

        states = StateSpace(contracts, max_depth = 10)
        report = fire_lasers(states)

        # augment with source code

        disassembly = ethcontract.get_disassembly()
        source = contractdata['source']

        deployedSourceMap = contractdata['deployedSourceMap'].split(";")

        mappings = []
        i = 0

        while(i < len(deployedSourceMap)):

            m = re.search(r"^(\d+):*(\d+)", deployedSourceMap[i])

            if (m):
                offset = m.group(1)
                length = m.group(2)
            else:
                m = re.search(r"^:(\d+)", deployedSourceMap[i])

                if m:
                    length = m.group(1)

            mappings.append((int(offset), int(length)))

            i += 1

        for key, issue in report.issues.items():

            index = helper.get_instruction_index(disassembly.instruction_list, issue.pc)

            if index:
                issue.code_start = mappings[index][0]
                issue.code_length = mappings[index][1]
                issue.code = source[mappings[index][0]: mappings[index][0] + mappings[index][1]]

        

        if len(report.issues):
            print("Analysis result for " + name + ":\n" + report.as_text())
        else:
            print("Analysis result for " + name + ": No issues found.") 


