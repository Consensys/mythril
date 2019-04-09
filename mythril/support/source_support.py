from mythril.solidity.soliditycontract import SolidityContract
from mythril.ethereum.evmcontract import EVMContract


class Source:
    """Class to handle to source data"""

    def __init__(self, source_type=None, source_format=None, source_list=None):
        """
        :param source_type: whether it is a solidity-file or evm-bytecode
        :param source_format: whether it is bytecode, ethereum-address or text
        :param source_list: List of files
        :param meta: meta data
        """
        self.source_type = source_type
        self.source_format = source_format
        self.source_list = source_list or []
        self._source_hash = []

    def get_source_from_contracts_list(self, contracts):
        """
        get the source data from the contracts list
        :param contracts: the list of contracts
        :return:
        """
        if contracts is None or len(contracts) == 0:
            return
        if isinstance(contracts[0], SolidityContract):
            self.source_type = "solidity-file"
            self.source_format = "text"
            for contract in contracts:
                self.source_list += [file.filename for file in contract.solidity_files]
                self._source_hash.append(contract.bytecode_hash)
                self._source_hash.append(contract.creation_bytecode_hash)
        elif isinstance(contracts[0], EVMContract):
            self.source_format = "evm-byzantium-bytecode"
            self.source_type = (
                "ethereum-address"
                if len(contracts[0].name) == 42 and contracts[0].name[0:2] == "0x"
                else "raw-bytecode"
            )
            for contract in contracts:
                if contract.creation_code:
                    self.source_list.append(contract.creation_bytecode_hash)
                if contract.code:
                    self.source_list.append(contract.bytecode_hash)
            self._source_hash = self.source_list

        else:
            assert False  # Fail hard

    def get_source_index(self, bytecode_hash: str) -> int:
        """
        Find the contract index in the list
        :param bytecode_hash: The contract hash
        :return: The index of the contract in the _source_hash list
        """
        return self._source_hash.index(bytecode_hash)
