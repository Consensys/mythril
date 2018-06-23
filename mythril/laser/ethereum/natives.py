# -*- coding: utf8 -*-

import copy
import hashlib

import coincurve

from py_ecc.secp256k1 import N as secp256k1n
from mythril.laser.ethereum.helper import ALL_BYTES, bytearray_to_int, concrete_int_to_bytes, sha3, zpad


def int_to_32bytes(i):   #used because int can't fit as bytes function's input
    o = [0] * 32
    for x in range(32):
        o[31 - x] = i & 0xff
        i >>= 8
    return bytes(o)


def ecrecover_to_pub(rawhash, v, r, s):
    try:
        pk = coincurve.PublicKey.from_signature_and_message(
            zpad(concrete_int_to_bytes(r), 32) + zpad(concrete_int_to_bytes(s), 32) +
            ALL_BYTES[v - 27],
            rawhash,
            hasher=None,
        )
        pub = pk.format(compressed=False)[1:]
    except BaseException:
        pub = b"\x00" * 64

    return pub


def extract32(data, i):
    if i >= len(data):
        return 0
    o = data[i: min(i + 32, len(data))]
    o.extend(bytearray(32 - len(o)))
    return bytearray_to_int(o)


def ecrecover(data):
    try:
        data = bytearray(data)
    except TypeError:
        return "ecrecover_"+str(data)
    message = b''.join(map(lambda x: ALL_BYTES[x], data[0:32]))
    v = extract32(data, 32)
    r = extract32(data, 64)
    s = extract32(data, 96)
    if r >= secp256k1n or s >= secp256k1n or v < 27 or v > 28:
        return []
    try:
        pub = ecrecover_to_pub(message, v, r, s)
    except Exception as e:
        return []
    o = [0] * 12 + [x for x in sha3(pub)[-20:]]
    return o


def sha256(data):
    try:
        data = bytes(data)
    except TypeError:
        return "sha256_"+str(data)
    return hashlib.sha256(data).digest()


def ripemd160(data):
    try:
        data = bytes(data)
    except TypeError:
        return "ripemd160_"+str(data)
    return 12*[0]+[i for i in hashlib.new('ripemd160', data).digest()]


def identity(data):
    return copy.copy(data)


def native_contracts(address, data):
    '''
    takes integer address 1, 2, 3, 4
    '''

    functions = (ecrecover, sha256, ripemd160, identity)
    return functions[address-1](data)
