import os
import json


def analyze_truffle_project():

    project_root = os.getcwd()
    
    build_dir = os.path.join(project_root, "build", "contracts")

    contract_files = os.listdir(build_dir)

    for contract_file in contract_files:

        with open(os.path.join(build_dir, contract_file)) as cf:
            contract = json.load(cf)

            name = contract['contractName']

            bytecode = contract['deployedBytecode']
            deployedSourceMap = contract['deployedSourceMap']

            