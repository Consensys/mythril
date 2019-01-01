from mythril.solidity.soliditycontract import SolidityContract
from mythril.ethereum.evmcontract import EVMContract


class Source:
    def __init__(
        self, source_type=None, source_format=None, source_list=None, meta=None
    ):
        self.source_type = source_type
        self.source_format = source_format
        self.source_list = []
        self.meta = meta

    def get_source_from_contracts_list(self, contracts):
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
