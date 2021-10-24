from ethereum import opcodes
from ethereum.utils import ceil32
from typing import Callable, Dict, Tuple, Union
from mythril.support.opcodes import OPCODES, STACK, GAS


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
