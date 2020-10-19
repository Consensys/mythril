from ethereum import opcodes
from ethereum.utils import ceil32
from typing import Callable, Dict, Tuple, Union


Z_OPERATOR_TUPLE = (0, 1)
UN_OPERATOR_TUPLE = (1, 1)
BIN_OPERATOR_TUPLE = (2, 1)
T_OPERATOR_TUPLE = (3, 1)
GAS = "gas"
STACK = "stack"

# Gas tuple contains (min_gas, max_gas)
# stack tuple contains (no_of_elements_popped, no_of_elements_pushed)

OPCODES = {
    "STOP": {GAS: (0, 0), STACK: (0, 0)},
    "ADD": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "MUL": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "SUB": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "DIV": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "SDIV": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "MOD": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "SMOD": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "ADDMOD": {GAS: (8, 8), STACK: BIN_OPERATOR_TUPLE},
    "MULMOD": {GAS: (8, 8), STACK: T_OPERATOR_TUPLE},
    "EXP": {GAS: (10, 340), STACK: BIN_OPERATOR_TUPLE},  # exponent max 2^32
    "SIGNEXTEND": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE},
    "LT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "GT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SLT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SGT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "EQ": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "AND": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "ISZERO": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE},
    "OR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "XOR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "NOT": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE},
    "BYTE": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SHL": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SHR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SAR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE},
    "SHA3": {
        GAS: (
            30,
            30 + 6 * 8,
        ),  # max can be larger, but usually storage location with 8 words
        STACK: BIN_OPERATOR_TUPLE,
    },
    "ADDRESS": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "BALANCE": {GAS: (700, 700), STACK: UN_OPERATOR_TUPLE},
    "ORIGIN": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CALLER": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CALLVALUE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CALLDATALOAD": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE},
    "CALLDATASIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CALLDATACOPY": {
        GAS: (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
        STACK: (3, 0),
    },
    "CODESIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CODECOPY": {
        GAS: (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556,
        STACK: (3, 0),
    },
    "GASPRICE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "EXTCODESIZE": {GAS: (700, 700), STACK: Z_OPERATOR_TUPLE},
    "EXTCODECOPY": {
        GAS: (700, 700 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
        STACK: (4, 0),
    },
    "EXTCODEHASH": {GAS: (700, 700), STACK: UN_OPERATOR_TUPLE},
    "RETURNDATASIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "RETURNDATACOPY": {GAS: (3, 3), STACK: (3, 0)},
    "BLOCKHASH": {GAS: (20, 20), STACK: UN_OPERATOR_TUPLE},
    "COINBASE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "TIMESTAMP": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "NUMBER": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "DIFFICULTY": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "GASLIMIT": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "CHAINID": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "SELFBALANCE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "POP": {GAS: (2, 2), STACK: (1, 0)},
    # assume 1KB memory r/w cost as upper bound
    "MLOAD": {GAS: (3, 96), STACK: UN_OPERATOR_TUPLE},
    "MSTORE": {GAS: (3, 98), STACK: (2, 0)},
    "MSTORE8": {GAS: (3, 98), STACK: (2, 0)},
    # assume 64 byte r/w cost as upper bound
    "SLOAD": {GAS: (800, 800), STACK: UN_OPERATOR_TUPLE},
    "SSTORE": {GAS: (5000, 25000), STACK: (1, 0)},
    "JUMP": {GAS: (8, 8), STACK: (1, 0)},
    "JUMPI": {GAS: (10, 10), STACK: (2, 0)},
    "PC": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "MSIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "GAS": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE},
    "JUMPDEST": {GAS: (1, 1), STACK: (0, 0)},
    "PUSH1": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH2": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH3": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH4": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH5": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH6": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH7": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH8": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH9": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH10": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH11": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH12": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH13": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH14": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH15": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH16": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH17": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH18": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH19": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH20": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH21": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH22": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH23": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH24": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH25": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH26": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH27": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH28": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH29": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH30": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH31": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "PUSH32": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP1": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP2": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP3": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP4": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP5": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP6": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP7": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP8": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP9": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP10": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP11": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP12": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP13": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP14": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP15": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "DUP16": {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE},
    "SWAP1": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP2": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP3": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP4": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP5": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP6": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP7": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP8": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP9": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP10": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP11": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP12": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP13": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP14": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP15": {GAS: (3, 3), STACK: (0, 0)},
    "SWAP16": {GAS: (3, 3), STACK: (0, 0)},
    # apparently Solidity only allows byte32 as input to the log
    # function. Virtually it could be as large as the block gas limit
    # allows, but let's stick to the reasonable standard here.
    # https://ethereum.stackexchange.com/a/1691
    "LOG0": {GAS: (375, 375 + 8 * 32), STACK: (2, 0)},
    "LOG1": {GAS: (2 * 375, 2 * 375 + 8 * 32), STACK: (3, 0)},
    "LOG2": {GAS: (3 * 375, 3 * 375 + 8 * 32), STACK: (4, 0)},
    "LOG3": {GAS: (4 * 375, 4 * 375 + 8 * 32), STACK: (5, 0)},
    "LOG4": {GAS: (5 * 375, 5 * 375 + 8 * 32), STACK: (6, 0)},
    "CREATE": {GAS: (32000, 32000), STACK: T_OPERATOR_TUPLE},
    "CREATE2": {
        GAS: (32000, 32000),  # TODO: Make the gas values dynamic
        STACK: (4, 1),
    },
    "CALL": {GAS: (700, 700 + 9000 + 25000), STACK: (7, 1)},
    "CALLCODE": {GAS: (700, 700 + 9000 + 25000), STACK: (7, 1)},
    "RETURN": {GAS: (0, 0), STACK: (2, 0)},
    "DELEGATECALL": {GAS: (700, 700 + 9000 + 25000), STACK: (6, 1)},
    "STATICCALL": {GAS: (700, 700 + 9000 + 25000), STACK: (6, 1)},
    "REVERT": {GAS: (0, 0), STACK: (2, 0)},
    "SUICIDE": {GAS: (5000, 30000), STACK: (1, 0)},
    "ASSERT_FAIL": {GAS: (0, 0), STACK: (0, 0)},
    "INVALID": {GAS: (0, 0), STACK: (0, 0)},
    "BEGINSUB": {GAS: (2, 2), STACK: (0, 0)},
    "JUMPSUB": {GAS: (10, 10), STACK: (1, 0)},
    "RETURNSUB": {GAS: (5, 5), STACK: (0, 0)},
}  # type: Dict[str, Dict[str, Tuple[int, int]]]


def calculate_sha3_gas(length: int):
    """

    :param length:
    :return:
    """
    gas_val = 30 + opcodes.GSHA3WORD * (ceil32(length) // 32)
    return gas_val, gas_val


def calculate_native_gas(size: int, contract: str):
    """

    :param size:
    :param contract:
    :return:
    """
    gas_value = 0
    word_num = ceil32(size) // 32
    if contract == "ecrecover":
        gas_value = opcodes.GECRECOVER
    elif contract == "sha256":
        gas_value = opcodes.GSHA256BASE + word_num * opcodes.GSHA256WORD
    elif contract == "ripemd160":
        gas_value = opcodes.GRIPEMD160BASE + word_num * opcodes.GRIPEMD160WORD
    elif contract == "identity":
        gas_value = opcodes.GIDENTITYBASE + word_num * opcodes.GIDENTITYWORD
    else:
        # TODO: Add gas for other precompiles, computation should be shifted to natives.py
        #  as some data isn't available here
        pass
    return gas_value, gas_value


def get_opcode_gas(opcode: str) -> Tuple[int, int]:
    return OPCODES[opcode][GAS]


def get_required_stack_elements(opcode: str) -> int:
    return OPCODES[opcode][STACK][0]
