import mythril.laser.ethereum.util as helper
from mythril.ether.ethcontract import ETHContract
from mythril.ether.util import get_solc_json
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


def get_contracts_from_file(input_file, solc_args=None):
    data = get_solc_json(input_file, solc_args=solc_args)
    for key, contract in data['contracts'].items():
        filename, name = key.split(":")
        if filename == input_file and len(contract['bin-runtime']):
            yield SolidityContract(input_file, name, solc_args)


class SolidityContract(ETHContract):

    def __init__(self, input_file, name=None, solc_args=None):

        data = get_solc_json(input_file, solc_args=solc_args)

        self.solidity_files = []

        for filename in data['sourceList']:
            with open(filename, 'r', encoding='utf-8') as file:
                code = file.read()
                self.solidity_files.append(SolidityFile(filename, code))

        has_contract = False

        # If a contract name has been specified, find the bytecode of that specific contract
        srcmap_constructor = []
        srcmap = []
        if name:
            for key, contract in sorted(data['contracts'].items()):
                filename, _name = key.split(":")

                if filename == input_file and name == _name and len(contract['bin-runtime']):
                    code = contract['bin-runtime']
                    creation_code = contract['bin']
                    srcmap = contract['srcmap-runtime'].split(";")
                    srcmap_constructor = contract['srcmap'].split(";")
                    has_contract = True
                    break

        # If no contract name is specified, get the last bytecode entry for the input file

        else:
            for key, contract in sorted(data['contracts'].items()):
                filename, name = key.split(":")

                if filename == input_file and len(contract['bin-runtime']):
                    code = contract['bin-runtime']
                    creation_code = contract['bin']
                    srcmap = contract['srcmap-runtime'].split(";")
                    srcmap_constructor = contract['srcmap'].split(";")
                    has_contract = True

        if not has_contract:
            raise NoContractFoundError

        self.mappings = []

        self.constructor_mappings = []

        self._get_solc_mappings(srcmap)
        self._get_solc_mappings(srcmap_constructor, constructor=True)

        super().__init__(code, creation_code, name=name)

    def get_source_info(self, address, constructor=False):
        disassembly = self.creation_disassemble if constructor else self.disassembly
        mappings = self.constructor_mappings if constructor else self.mappings
        index = helper.get_instruction_index(disassembly.instruction_list, address)

        solidity_file = self.solidity_files[mappings[index].solidity_file_idx]

        filename = solidity_file.filename

        offset = mappings[index].offset
        length = mappings[index].length

        code = solidity_file.data.encode('utf-8')[offset:offset + length].decode('utf-8', errors="ignore")
        lineno = mappings[index].lineno

        return SourceCodeInfo(filename, lineno, code)

    def _get_solc_mappings(self, srcmap, constructor=False):
        mappings = self.constructor_mappings if constructor else self.mappings
        for item in srcmap:
            mapping = item.split(":")

            if len(mapping) > 0 and len(mapping[0]) > 0:
                offset = int(mapping[0])

            if len(mapping) > 1 and len(mapping[1]) > 0:
                length = int(mapping[1])

            if len(mapping) > 2 and len(mapping[2]) > 0:
                idx = int(mapping[2])
            lineno = self.solidity_files[idx].data.encode('utf-8')[0:offset].count('\n'.encode('utf-8')) + 1

            mappings.append(SourceMapping(idx, offset, length, lineno))
