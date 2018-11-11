# -*- coding: utf8 -*-

import hashlib
import logging

from ethereum.utils import ecrecover_to_pub
from py_ecc.secp256k1 import N as secp256k1n
from rlp.utils import ALL_BYTES

from mythril.laser.ethereum.util import bytearray_to_int, sha3, get_concrete_int
from z3 import Concat, simplify


class NativeContractException(Exception):
    pass


def int_to_32bytes(i):  # used because int can't fit as bytes function's input
    o = [0] * 32
    for x in range(32):
        o[31 - x] = i & 0xFF
        i >>= 8
    return bytes(o)


def extract32(data, i):
    if i >= len(data):
        return 0
    o = data[i : min(i + 32, len(data))]
    o.extend(bytearray(32 - len(o)))
    return bytearray_to_int(o)


def ecrecover(data):

    try:
        data = bytearray(data)
        v = extract32(data, 32)
        r = extract32(data, 64)
        s = extract32(data, 96)
    except TypeError:
        raise NativeContractException

    message = b"".join([ALL_BYTES[x] for x in data[0:32]])
    if r >= secp256k1n or s >= secp256k1n or v < 27 or v > 28:
        return []
    try:
        pub = ecrecover_to_pub(message, v, r, s)
    except Exception as e:
        logging.debug("An error has occured while extracting public key: " + e)
        return []
    o = [0] * 12 + [x for x in sha3(pub)[-20:]]
    return o


def sha256(data):
    try:
        data = bytes(data)
    except TypeError:
        raise NativeContractException
    return hashlib.sha256(data).digest()


def ripemd160(data):
    try:
        data = bytes(data)
    except TypeError:
        raise NativeContractException
    return 12 * [0] + [i for i in hashlib.new("ripemd160", data).digest()]


def identity(data):
    # Group up into an array of 32 byte words instead
    # of an array of bytes. If saved to memory, 32 byte
    # words are currently needed, but a correct memory
    # implementation would be byte indexed for the most
    # part.
    return data
    result = []
    for i in range(0, len(data), 32):
        result.append(simplify(Concat(data[i : i + 32])))
    return result


def native_contracts(address, data):
    """
    takes integer address 1, 2, 3, 4
    """

    functions = (ecrecover, sha256, ripemd160, identity)

    try:
        data = [get_concrete_int(e) for e in data._calldata]
    except TypeError:
        # Symbolic calldata
        data = data._calldata

    return functions[address - 1](data)
