import mythril.laser.ethereum.helper as helper
from mythril.ether.ethcontract import ETHContract
from mythril.ether.util import *
from mythril.exceptions import NoContractFoundError

class SourceMapping:

    def __init__(self, solidity_file_idx, offset, length, lineno):
        self.solidity_file_idx = solidity_file_idx
        self.offset = offset
        self.length = length
        self.lineno = lineno


class SolidityFile:

    def __init__(self, filename, data):
        self.filename = filename
        self.data = data


class SourceCodeInfo:

    def __init__(self, filename, lineno, code):
        self.filename = filename
        self.lineno = lineno
        self.code = code


class SolidityContract(ETHContract):

    def __init__(self, input_file, name=None, solc_args=None):

        data = get_solc_json(input_file, solc_args=solc_args)

        self.solidity_files = []

        for filename in data['sourceList']:
            with open(filename, 'r') as file:
                code = file.read()
                self.solidity_files.append(SolidityFile(filename, code))

        has_contract = False

        # If a contract name has been specified, find the bytecode of that specific contract

        if name:
            for key, contract in data['contracts'].items():
                filename, _name = key.split(":")

                if filename == input_file and name == _name:
                    name = name
                    code = contract['bin-runtime']
                    creation_code = contract['bin']
                    srcmap = contract['srcmap-runtime'].split(";")
                    has_contract = True
                    break

        # If no contract name is specified, get the last bytecode entry for the input file

        else:
            for key, contract in data['contracts'].items():
                filename, name = key.split(":")

                if filename == input_file and len(contract['bin-runtime']):
                    name = name
                    code = contract['bin-runtime']
                    creation_code = contract['bin']
                    srcmap = contract['srcmap-runtime'].split(";")
                    has_contract = True

        if not has_contract:
            raise NoContractFoundError

        self.mappings = []

        for item in srcmap:
            mapping = item.split(":")

            if len(mapping) > 0 and len(mapping[0]) > 0:
                offset = int(mapping[0])

            if len(mapping) > 1 and len(mapping[1]) > 0:
                length = int(mapping[1])

            if len(mapping) > 2 and len(mapping[2]) > 0:
                idx = int(mapping[2])

            lineno = self.solidity_files[idx].data[0:offset].count('\n') + 1

            self.mappings.append(SourceMapping(idx, offset, length, lineno))

        super().__init__(code, creation_code, name=name)

    def get_source_info(self, address):

        index = helper.get_instruction_index(self.disassembly.instruction_list, address)

        solidity_file = self.solidity_files[self.mappings[index].solidity_file_idx]

        filename = solidity_file.filename

        offset = self.mappings[index].offset
        length = self.mappings[index].length

        code = solidity_file.data[offset:offset + length]
        lineno = self.mappings[index].lineno

        return SourceCodeInfo(filename, lineno, code)
