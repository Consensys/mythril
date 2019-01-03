from mythril.solidity.soliditycontract import SolidityContract
from mythril.ethereum.evmcontract import EVMContract


class Source:
    """Class to handle to source data"""

    def __init__(
        self, source_type=None, source_format=None, source_list=None, meta=None
    ):
        """
        :param source_type: whether it is a solidity-file or evm-bytecode
        :param source_format: whether it is bytecode, ethereum-address or text
        :param source_list: List of files
        :param meta: meta data
        """
        self.source_type = source_type
        self.source_format = source_format
        self.source_list = []
        self.meta = meta

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
        elif isinstance(contracts[0], EVMContract):
            self.source_format = "evm-byzantium-bytecode"
            self.source_type = (
                "raw-bytecode" if contracts[0].name == "MAIN" else "ethereum-address"
            )
            for contract in contracts:
                self.source_list.append(contract.bytecode_hash)

        else:
            assert False  # Fail hard
