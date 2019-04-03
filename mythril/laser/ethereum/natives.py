"""This nodule defines helper functions to deal with native calls."""

import hashlib
import logging
from typing import List, Union

from ethereum.utils import ecrecover_to_pub
from py_ecc.secp256k1 import N as secp256k1n
from rlp.utils import ALL_BYTES

from mythril.laser.ethereum.state.calldata import BaseCalldata, ConcreteCalldata
from mythril.laser.ethereum.util import bytearray_to_int, extract_copy
from ethereum.utils import sha3, big_endian_to_int, safe_ord, zpad, int_to_big_endian
from mythril.laser.smt import Concat, simplify

log = logging.getLogger(__name__)


class NativeContractException(Exception):
    """An exception denoting an error during a native call."""

    pass


def int_to_32bytes(
    i: int
) -> bytes:  # used because int can't fit as bytes function's input
    """

    :param i:
    :return:
    """
    o = [0] * 32
    for x in range(32):
        o[31 - x] = i & 0xFF
        i >>= 8
    return bytes(o)


def extract32(data: bytearray, i: int) -> int:
    """

    :param data:
    :param i:
    :return:
    """
    if i >= len(data):
        return 0
    o = data[i : min(i + 32, len(data))]
    o.extend(bytearray(32 - len(o)))
    return bytearray_to_int(o)


def ecrecover(data: List[int]) -> List[int]:
    """

    :param data:
    :return:
    """
    # TODO: Add type hints
    try:
        byte_data = bytearray(data)
        v = extract32(byte_data, 32)
        r = extract32(byte_data, 64)
        s = extract32(byte_data, 96)
    except TypeError:
        raise NativeContractException

    message = b"".join([ALL_BYTES[x] for x in byte_data[0:32]])
    if r >= secp256k1n or s >= secp256k1n or v < 27 or v > 28:
        return []
    try:
        pub = ecrecover_to_pub(message, v, r, s)
    except Exception as e:
        log.debug("An error has occured while extracting public key: " + str(e))
        return []
    o = [0] * 12 + [x for x in sha3(pub)[-20:]]
    return list(bytearray(o))


def sha256(data: List[int]) -> List[int]:
    """

    :param data:
    :return:
    """
    try:
        byte_data = bytes(data)
    except TypeError:
        raise NativeContractException
    return list(bytearray(hashlib.sha256(byte_data).digest()))


def ripemd160(data: List[int]) -> List[int]:
    """

    :param data:
    :return:
    """
    try:
        bytes_data = bytes(data)
    except TypeError:
        raise NativeContractException
    digest = hashlib.new("ripemd160", bytes_data).digest()
    padded = 12 * [0] + list(digest)
    return list(bytearray(bytes(padded)))


def identity(data: List[int]) -> List[int]:
    """

    :param data:
    :return:
    """
    # Group up into an array of 32 byte words instead
    # of an array of bytes. If saved to memory, 32 byte
    # words are currently needed, but a correct memory
    # implementation would be byte indexed for the most
    # part.
    return data


def mod_exp(data: List[int]) -> List[int]:
    """
    Modular Exponentiation
    :param data: Data with <length_of_BASE> <length_of_EXPONENT> <length_of_MODULUS> <BASE> <EXPONENT> <MODULUS>
    :return: modular exponentiation
    """
    data = bytearray(data)
    baselen = extract32(data, 0)
    explen = extract32(data, 32)
    modlen = extract32(data, 64)
    if baselen == 0:
        return [0] * modlen
    if modlen == 0:
        return []

    first_exp_bytes = extract32(data, 96 + baselen) >> (8 * max(32 - explen, 0))
    bitlength = -1
    while first_exp_bytes:
        bitlength += 1
        first_exp_bytes >>= 1

    base = bytearray(baselen)
    extract_copy(data, base, 0, 96, baselen)
    exp = bytearray(explen)
    extract_copy(data, exp, 0, 96 + baselen, explen)
    mod = bytearray(modlen)
    extract_copy(data, mod, 0, 96 + baselen + explen, modlen)
    if big_endian_to_int(mod) == 0:
        return [0] * modlen
    o = pow(big_endian_to_int(base), big_endian_to_int(exp), big_endian_to_int(mod))
    return [safe_ord(x) for x in zpad(int_to_big_endian(o), modlen)]


def native_contracts(address: int, data: BaseCalldata) -> List[int]:
    """Takes integer address 1, 2, 3, 4.

    :param address:
    :param data:
    :return:
    """
    functions = (ecrecover, sha256, ripemd160, identity, mod_exp)

    # TODO: Handle these
    if isinstance(data, ConcreteCalldata):
        concrete_data = data.concrete(None)
    else:
        raise NativeContractException()

    return functions[address - 1](concrete_data)
