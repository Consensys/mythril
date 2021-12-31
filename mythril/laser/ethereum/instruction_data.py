from eth._utils.numeric import ceil32
from typing import Tuple
from mythril.support.opcodes import OPCODES, STACK, GAS
from eth.constants import (
    GAS_ECRECOVER,
    GAS_SHA256WORD,
    GAS_SHA256,
    GAS_RIPEMD160,
    GAS_RIPEMD160WORD,
    GAS_IDENTITY,
    GAS_IDENTITYWORD,
    GAS_SHA3WORD,
    GAS_SHA3,
)


def calculate_sha3_gas(length: int):
    """

    :param length:
    :return:
    """
    gas_val = GAS_SHA3 + GAS_SHA3WORD * (ceil32(length) // 32)
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
        gas_value = GAS_ECRECOVER
    elif contract == "sha256":
        gas_value = GAS_SHA256 + word_num * GAS_SHA256WORD
    elif contract == "ripemd160":
        gas_value = GAS_RIPEMD160 + word_num * GAS_RIPEMD160WORD
    elif contract == "identity":
        gas_value = GAS_IDENTITY + word_num * GAS_IDENTITYWORD
    else:
        # TODO: Add gas for other precompiles, computation should be shifted to natives.py
        #  as some data isn't available here
        pass
    return gas_value, gas_value


def get_opcode_gas(opcode: str) -> Tuple[int, int]:
    return OPCODES[opcode][GAS]


def get_required_stack_elements(opcode: str) -> int:
    return OPCODES[opcode][STACK][0]
