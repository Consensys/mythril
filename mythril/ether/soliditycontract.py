from mythril.ether.ethcontract import ETHContract
from mythril.ether.util import *
from mythril.exceptions import NoContractFoundError

class SourceMapping:

    def __init__(self, solidity_file_idx, offset, length):
        self.solidity_file_idx = solidity_file_idx
        self.offset = offset
        self.length = length

class SolidityFile:

    def __init__(self, filename, data):
        self.filename = filename
        self.data = data

class SolidityContract(ETHContract):

    def __init__(self, input_file, contract_name = None):

        data = get_solc_json(input_file)

        self.solidity_files = []

        for filename in data['sourceList']:
            with open(filename, 'r') as file:
                code = file.read()
                self.solidity_files.append(SolidityFile(filename, code))

        has_contract = False

        for key, contract in data['contracts'].items():
            filename, name = key.split(":")

            if filename == input_file and len(contract['bin-runtime']):
                self.name = name
                self.code = contract['bin-runtime']
                self.creation_code = contract['bin']
                has_contract = True
                break

        if not has_contract:
            raise NoContractFoundError

        self.mappings = []

        srcmap = contract['srcmap-runtime'].split(";")

        for item in srcmap:

            mapping = item.split(":")

            if len(mapping) > 0 and len(mapping[0]) > 0:
                offset = int(mapping[0])

            if len(mapping) > 1 and len(mapping[1]) > 0:
                length = int(mapping[1])
            
            if len(mapping) > 2 and len(mapping[2]) > 0:
                idx = int(mapping[2])

            self.mappings.append(SourceMapping(idx, offset, length))

        super().__init__(self.code, self.creation_code, name)
