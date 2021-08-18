from typing import Dict, List
from typing_extensions import TypedDict


class AccountData(TypedDict):
    balance: str
    code: str
    nonce: int
    storage: dict


class InitialState(TypedDict):
    accounts: Dict[str, AccountData]


class TransactionData(TypedDict):
    address: str
    blockCoinbase: str
    blockDifficulty: str
    blockGasLimit: str
    blockNumber: str
    blockTime: str
    calldata: str
    gasLimit: str
    gasPrice: str
    input: str
    name: str
    origin: str
    value: str


class ConcreteData(TypedDict):
    initialState: InitialState
    steps: List[TransactionData]
