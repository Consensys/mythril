# This pyethereum opcodes file with added opcodes
from typing import Dict, Tuple

opcodes = {
    0x00: ("STOP", 0, 0, 0),
    0x01: ("ADD", 2, 1, 3),
    0x02: ("MUL", 2, 1, 5),
    0x03: ("SUB", 2, 1, 3),
    0x04: ("DIV", 2, 1, 5),
    0x05: ("SDIV", 2, 1, 5),
    0x06: ("MOD", 2, 1, 5),
    0x07: ("SMOD", 2, 1, 5),
    0x08: ("ADDMOD", 3, 1, 8),
    0x09: ("MULMOD", 3, 1, 8),
    0x0A: ("EXP", 2, 1, 10),
    0x0B: ("SIGNEXTEND", 2, 1, 5),
    0x10: ("LT", 2, 1, 3),
    0x11: ("GT", 2, 1, 3),
    0x12: ("SLT", 2, 1, 3),
    0x13: ("SGT", 2, 1, 3),
    0x14: ("EQ", 2, 1, 3),
    0x15: ("ISZERO", 1, 1, 3),
    0x16: ("AND", 2, 1, 3),
    0x17: ("OR", 2, 1, 3),
    0x18: ("XOR", 2, 1, 3),
    0x19: ("NOT", 1, 1, 3),
    0x1A: ("BYTE", 2, 1, 3),
    0x1B: ("SHL", 2, 1, 3),
    0x1C: ("SHR", 2, 1, 3),
    0x1D: ("SAR", 2, 1, 3),
    0x20: ("SHA3", 2, 1, 30),
    0x30: ("ADDRESS", 0, 1, 2),
    0x31: ("BALANCE", 1, 1, 20),  # now 400
    0x32: ("ORIGIN", 0, 1, 2),
    0x33: ("CALLER", 0, 1, 2),
    0x34: ("CALLVALUE", 0, 1, 2),
    0x35: ("CALLDATALOAD", 1, 1, 3),
    0x36: ("CALLDATASIZE", 0, 1, 2),
    0x37: ("CALLDATACOPY", 3, 0, 3),
    0x38: ("CODESIZE", 0, 1, 2),
    0x39: ("CODECOPY", 3, 0, 3),
    0x3A: ("GASPRICE", 0, 1, 2),
    0x3B: ("EXTCODESIZE", 1, 1, 20),  # now 700
    0x3C: ("EXTCODECOPY", 4, 0, 20),  # now 700
    0x3D: ("RETURNDATASIZE", 0, 1, 2),
    0x3E: ("RETURNDATACOPY", 3, 0, 3),
    0x3F: ("EXTCODEHASH", 3, 0, 3),
    0x40: ("BLOCKHASH", 1, 1, 20),
    0x41: ("COINBASE", 0, 1, 2),
    0x42: ("TIMESTAMP", 0, 1, 2),
    0x43: ("NUMBER", 0, 1, 2),
    0x44: ("DIFFICULTY", 0, 1, 2),
    0x45: ("GASLIMIT", 0, 1, 2),
    0x46: ("CHAINID", 0, 1, 2),
    0x47: ("SELFBALANCE", 0, 1, 5),
    0x50: ("POP", 1, 0, 2),
    0x51: ("MLOAD", 1, 1, 3),
    0x52: ("MSTORE", 2, 0, 3),
    0x53: ("MSTORE8", 2, 0, 3),
    0x54: ("SLOAD", 1, 1, 50),  # 200 now
    0x55: ("SSTORE", 2, 0, 0),
    0x56: ("JUMP", 1, 0, 8),
    0x57: ("JUMPI", 2, 0, 10),
    0x58: ("PC", 0, 1, 2),
    0x59: ("MSIZE", 0, 1, 2),
    0x5A: ("GAS", 0, 1, 2),
    0x5B: ("JUMPDEST", 0, 0, 1),
    0x5C: ("BEGINSUB", 0, 0, 2),
    0x5D: ("RETURNSUB", 0, 0, 5),
    0x5E: ("JUMPSUB", 1, 0, 10),
    0xA0: ("LOG0", 2, 0, 375),
    0xA1: ("LOG1", 3, 0, 750),
    0xA2: ("LOG2", 4, 0, 1125),
    0xA3: ("LOG3", 5, 0, 1500),
    0xA4: ("LOG4", 6, 0, 1875),
    0xF0: ("CREATE", 3, 1, 32000),
    0xF1: ("CALL", 7, 1, 40),  # 700 now
    0xF2: ("CALLCODE", 7, 1, 40),  # 700 now
    0xF3: ("RETURN", 2, 0, 0),
    0xF4: ("DELEGATECALL", 6, 1, 40),  # 700 now
    0xF5: ("CREATE2", 3, 1, 32000),
    0xFA: ("STATICCALL", 6, 1, 40),
    0xFD: ("REVERT", 2, 0, 0),
    0xFF: ("SUICIDE", 1, 0, 0),  # 5000 now
}  # type: Dict[int, Tuple[str, int, int, int]]

opcodesMetropolis = {0x3D, 0x3E, 0xFA, 0xFD}

for i in range(1, 33):
    opcodes[0x5F + i] = ("PUSH" + str(i), 0, 1, 3)

for i in range(1, 17):
    opcodes[0x7F + i] = ("DUP" + str(i), i, i + 1, 3)
    opcodes[0x8F + i] = ("SWAP" + str(i), i + 1, i + 1, 3)

reverse_opcodes = {}
for o in opcodes:
    vars()[opcodes[o][0]] = opcodes[o]
    reverse_opcodes[opcodes[o][0]] = o
