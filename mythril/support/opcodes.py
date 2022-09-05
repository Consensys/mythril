from typing import Dict


Z_OPERATOR_TUPLE = (0, 1)
UN_OPERATOR_TUPLE = (1, 1)
BIN_OPERATOR_TUPLE = (2, 1)
T_OPERATOR_TUPLE = (3, 1)
GAS = "gas"
STACK = "stack"
ADDRESS = "address"

# Gas tuple contains (min_gas, max_gas)
# stack tuple contains (no_of_elements_popped, no_of_elements_pushed)

# TODO: Make this more specific when TypedDict supports key re-usage.
OPCODES: Dict = {
    "STOP": {GAS: (0, 0), STACK: (0, 0), ADDRESS: 0x00},
    "ADD": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x01},
    "MUL": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x02},
    "SUB": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x03},
    "DIV": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x04},
    "SDIV": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x05},
    "MOD": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x06},
    "SMOD": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x07},
    "ADDMOD": {GAS: (8, 8), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x08},
    "MULMOD": {GAS: (8, 8), STACK: T_OPERATOR_TUPLE, ADDRESS: 0x09},
    "EXP": {
        GAS: (10, 340),
        STACK: BIN_OPERATOR_TUPLE,
        ADDRESS: 0x0A,
    },  # exponent max 2^32
    "SIGNEXTEND": {GAS: (5, 5), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x0B},
    "LT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x10},
    "GT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x11},
    "SLT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x12},
    "SGT": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x13},
    "EQ": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x14},
    "ISZERO": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x15},
    "AND": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x16},
    "OR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x17},
    "XOR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x18},
    "NOT": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x19},
    "BYTE": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x1A},
    "SHL": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x1B},
    "SHR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x1C},
    "SAR": {GAS: (3, 3), STACK: BIN_OPERATOR_TUPLE, ADDRESS: 0x1D},
    "SHA3": {
        GAS: (
            30,
            30 + 6 * 8,
        ),  # max can be larger, but usually storage location with 8 words
        STACK: BIN_OPERATOR_TUPLE,
        ADDRESS: 0x20,
    },
    "ADDRESS": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x30},
    "BALANCE": {GAS: (700, 700), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x31},
    "ORIGIN": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x32},
    "CALLER": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x33},
    "CALLVALUE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x34},
    "CALLDATALOAD": {GAS: (3, 3), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x35},
    "CALLDATASIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x36},
    "CALLDATACOPY": {
        GAS: (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
        STACK: (3, 0),
        ADDRESS: 0x37,
    },
    "CODESIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x38},
    "CODECOPY": {
        GAS: (2, 2 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556,
        STACK: (3, 0),
        ADDRESS: 0x39,
    },
    "GASPRICE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x3A},
    "EXTCODESIZE": {GAS: (700, 700), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x3B},
    "EXTCODECOPY": {
        GAS: (700, 700 + 3 * 768),  # https://ethereum.stackexchange.com/a/47556
        STACK: (4, 0),
        ADDRESS: 0x3C,
    },
    "EXTCODEHASH": {GAS: (700, 700), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x3F},
    "RETURNDATASIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x3D},
    "RETURNDATACOPY": {GAS: (3, 3), STACK: (3, 0), ADDRESS: 0x3E},
    "BLOCKHASH": {GAS: (20, 20), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x40},
    "COINBASE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x41},
    "TIMESTAMP": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x42},
    "NUMBER": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x43},
    "DIFFICULTY": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x44},
    "GASLIMIT": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x45},
    "CHAINID": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x46},
    "SELFBALANCE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x47},
    "BASEFEE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x48},
    "POP": {GAS: (2, 2), STACK: (1, 0), ADDRESS: 0x50},
    # assume 1KB memory r/w cost as upper bound
    "MLOAD": {GAS: (3, 96), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x51},
    "MSTORE": {GAS: (3, 98), STACK: (2, 0), ADDRESS: 0x52},
    "MSTORE8": {GAS: (3, 98), STACK: (2, 0), ADDRESS: 0x53},
    # assume 64 byte r/w cost as upper bound
    "SLOAD": {GAS: (800, 800), STACK: UN_OPERATOR_TUPLE, ADDRESS: 0x54},
    "SSTORE": {GAS: (5000, 25000), STACK: (1, 0), ADDRESS: 0x55},
    "JUMP": {GAS: (8, 8), STACK: (1, 0), ADDRESS: 0x56},
    "JUMPI": {GAS: (10, 10), STACK: (2, 0), ADDRESS: 0x57},
    "PC": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x58},
    "MSIZE": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x59},
    "GAS": {GAS: (2, 2), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x5A},
    "JUMPDEST": {GAS: (1, 1), STACK: (0, 0), ADDRESS: 0x5B},
    "BEGINSUB": {GAS: (2, 2), STACK: (0, 0), ADDRESS: 0x5C},
    "RETURNSUB": {GAS: (5, 5), STACK: (0, 0), ADDRESS: 0x5D},
    "JUMPSUB": {GAS: (10, 10), STACK: (1, 0), ADDRESS: 0x5E},
    # apparently Solidity only allows byte32 as input to the log
    # function. Virtually it could be as large as the block gas limit
    # allows, but let's stick to the reasonable standard here.
    # https://ethereum.stackexchange.com/a/1691
    "LOG0": {GAS: (375, 375 + 8 * 32), STACK: (2, 0), ADDRESS: 0xA0},
    "LOG1": {GAS: (2 * 375, 2 * 375 + 8 * 32), STACK: (3, 0), ADDRESS: 0xA1},
    "LOG2": {GAS: (3 * 375, 3 * 375 + 8 * 32), STACK: (4, 0), ADDRESS: 0xA2},
    "LOG3": {GAS: (4 * 375, 4 * 375 + 8 * 32), STACK: (5, 0), ADDRESS: 0xA3},
    "LOG4": {GAS: (5 * 375, 5 * 375 + 8 * 32), STACK: (6, 0), ADDRESS: 0xA4},
    "CREATE": {GAS: (32000, 32000), STACK: T_OPERATOR_TUPLE, ADDRESS: 0xF0},
    "CREATE2": {
        GAS: (32000, 32000),  # TODO: Make the gas values dynamic
        STACK: (4, 1),
        ADDRESS: 0xF5,
    },
    "CALL": {GAS: (700, 700 + 9000 + 25000), STACK: (7, 1), ADDRESS: 0xF1},
    "CALLCODE": {GAS: (700, 700 + 9000 + 25000), STACK: (7, 1), ADDRESS: 0xF2},
    "RETURN": {GAS: (0, 0), STACK: (2, 0), ADDRESS: 0xF3},
    "DELEGATECALL": {GAS: (700, 700 + 9000 + 25000), STACK: (6, 1), ADDRESS: 0xF4},
    "STATICCALL": {GAS: (700, 700 + 9000 + 25000), STACK: (6, 1), ADDRESS: 0xFA},
    "REVERT": {GAS: (0, 0), STACK: (2, 0), ADDRESS: 0xFD},
    "SELFDESTRUCT": {GAS: (5000, 30000), STACK: (1, 0), ADDRESS: 0xFF},
    "INVALID": {GAS: (0, 0), STACK: (0, 0), ADDRESS: 0xFE},
}

for i in range(1, 33):
    OPCODES[f"PUSH{i}"] = {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x5F + i}

for i in range(1, 17):
    OPCODES[f"DUP{i}"] = {GAS: (3, 3), STACK: (0, 0), ADDRESS: 0x7F + i}
    OPCODES[f"SWAP{i}"] = {GAS: (3, 3), STACK: Z_OPERATOR_TUPLE, ADDRESS: 0x8F + i}

ADDRESS_OPCODE_MAPPING = {}

for opcode, opcode_data in OPCODES.items():
    ADDRESS_OPCODE_MAPPING[opcode_data[ADDRESS]] = opcode
