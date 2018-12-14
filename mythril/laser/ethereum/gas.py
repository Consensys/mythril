"""This module contains functions for dynamic gas calculation and a gas cost table."""
from ethereum import opcodes
from ethereum.utils import ceil32


def calculate_native_gas(size: int, contract: str):
    """

    :param size:
    :param contract:
    :return:
    """
    gas_value = None
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
        raise ValueError("Unknown contract type {}".format(contract))
    return gas_value, gas_value


def calculate_sha3_gas(length: int):
    """

    :param length:
    :return:
    """
    gas_val = 30 + opcodes.GSHA3WORD * (ceil32(length) // 32)
    return gas_val, gas_val


# opcode -> (min_gas, max_gas)
OPCODE_GAS = {
    "STOP": (0, 0),
    "ADD": (3, 3),
    "MUL": (5, 5),
    "SUB": (3, 3),
    "DIV": (5, 5),
    "SDIV": (5, 5),
    "MOD": (5, 5),
    "SMOD": (5, 5),
    "ADDMOD": (8, 8),
    "MULMOD": (8, 8),
    "EXP": (10, 340),  # exponent max 2^32
    "SIGNEXTEND": (5, 5),
    "LT": (3, 3),
    "GT": (3, 3),
    "SLT": (3, 3),
    "SGT": (3, 3),
    "EQ": (3, 3),
    "ISZERO": (3, 3),
    "AND": (3, 3),
    "OR": (3, 3),
    "XOR": (3, 3),
    "NOT": (3, 3),
    "BYTE": (3, 3),
    "SHA3": (
        30,
        30 + 6 * 8,
    ),  # max can be larger, but usually storage location with 8 words
    "SHA3_FUNC": calculate_sha3_gas,
    "ADDRESS": (2, 2),
    "BALANCE": (400, 400),
    "ORIGIN": (2, 2),
    "CALLER": (2, 2),
    "CALLVALUE": (2, 2),
    "CALLDATALOAD": (3, 3),
    "CALLDATASIZE": (2, 2),
    "CALLDATACOPY": (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
    "CODESIZE": (2, 2),
    "CODECOPY": (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556,
    "GASPRICE": (2, 2),
    "EXTCODESIZE": (700, 700),
    "EXTCODECOPY": (700, 700 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
    "RETURNDATASIZE": (2, 2),
    "RETURNDATACOPY": (3, 3),
    "BLOCKHASH": (20, 20),
    "COINBASE": (2, 2),
    "TIMESTAMP": (2, 2),
    "NUMBER": (2, 2),
    "DIFFICULTY": (2, 2),
    "GASLIMIT": (2, 2),
    "POP": (2, 2),
    # assume 1KB memory r/w cost as upper bound
    "MLOAD": (3, 96),
    "MSTORE": (3, 98),
    "MSTORE8": (3, 98),
    # assume 64 byte r/w cost as upper bound
    "SLOAD": (400, 400),
    "SSTORE": (5000, 25000),
    "JUMP": (8, 8),
    "JUMPI": (10, 10),
    "PC": (2, 2),
    "MSIZE": (2, 2),
    "GAS": (2, 2),
    "JUMPDEST": (1, 1),
    "PUSH1": (3, 3),
    "PUSH2": (3, 3),
    "PUSH3": (3, 3),
    "PUSH4": (3, 3),
    "PUSH5": (3, 3),
    "PUSH6": (3, 3),
    "PUSH7": (3, 3),
    "PUSH8": (3, 3),
    "PUSH9": (3, 3),
    "PUSH10": (3, 3),
    "PUSH11": (3, 3),
    "PUSH12": (3, 3),
    "PUSH13": (3, 3),
    "PUSH14": (3, 3),
    "PUSH15": (3, 3),
    "PUSH16": (3, 3),
    "PUSH17": (3, 3),
    "PUSH18": (3, 3),
    "PUSH19": (3, 3),
    "PUSH20": (3, 3),
    "PUSH21": (3, 3),
    "PUSH22": (3, 3),
    "PUSH23": (3, 3),
    "PUSH24": (3, 3),
    "PUSH25": (3, 3),
    "PUSH26": (3, 3),
    "PUSH27": (3, 3),
    "PUSH28": (3, 3),
    "PUSH29": (3, 3),
    "PUSH30": (3, 3),
    "PUSH31": (3, 3),
    "PUSH32": (3, 3),
    "DUP1": (3, 3),
    "DUP2": (3, 3),
    "DUP3": (3, 3),
    "DUP4": (3, 3),
    "DUP5": (3, 3),
    "DUP6": (3, 3),
    "DUP7": (3, 3),
    "DUP8": (3, 3),
    "DUP9": (3, 3),
    "DUP10": (3, 3),
    "DUP11": (3, 3),
    "DUP12": (3, 3),
    "DUP13": (3, 3),
    "DUP14": (3, 3),
    "DUP15": (3, 3),
    "DUP16": (3, 3),
    "SWAP1": (3, 3),
    "SWAP2": (3, 3),
    "SWAP3": (3, 3),
    "SWAP4": (3, 3),
    "SWAP5": (3, 3),
    "SWAP6": (3, 3),
    "SWAP7": (3, 3),
    "SWAP8": (3, 3),
    "SWAP9": (3, 3),
    "SWAP10": (3, 3),
    "SWAP11": (3, 3),
    "SWAP12": (3, 3),
    "SWAP13": (3, 3),
    "SWAP14": (3, 3),
    "SWAP15": (3, 3),
    "SWAP16": (3, 3),
    # apparently Solidity only allows byte32 as input to the log
    # function. Virtually it could be as large as the block gas limit
    # allows, but let's stick to the reasonable standard here.
    # https://ethereum.stackexchange.com/a/1691
    "LOG0": (375, 375 + 8 * 32),
    "LOG1": (2 * 375, 2 * 375 + 8 * 32),
    "LOG2": (3 * 375, 3 * 375 + 8 * 32),
    "LOG3": (4 * 375, 4 * 375 + 8 * 32),
    "LOG4": (5 * 375, 5 * 375 + 8 * 32),
    "CREATE": (32000, 32000),
    "CALL": (700, 700 + 9000 + 25000),
    "NATIVE_COST": calculate_native_gas,
    "CALLCODE": (700, 700 + 9000 + 25000),
    "RETURN": (0, 0),
    "DELEGATECALL": (700, 700 + 9000 + 25000),
    "STATICCALL": (700, 700 + 9000 + 25000),
    "REVERT": (0, 0),
    "SUICIDE": (5000, 30000),
    "ASSERT_FAIL": (0, 0),
    "INVALID": (0, 0),
}
