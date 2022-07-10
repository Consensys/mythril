"""This module contains utility functions for the Mythril support package."""
from functools import lru_cache
from typing import Dict
import logging
from eth_hash.auto import keccak

log = logging.getLogger(__name__)


class Singleton(type):
    """A metaclass type implementing the singleton pattern."""

    _instances = {}  # type: Dict

    def __call__(cls, *args, **kwargs):
        """Delegate the call to an existing resource or a a new one.

        This is not thread- or process-safe by default. It must be protected with
        a lock.

        :param args:
        :param kwargs:
        :return:
        """
        if cls not in cls._instances:
            cls._instances[cls] = super(Singleton, cls).__call__(*args, **kwargs)
        return cls._instances[cls]


@lru_cache(maxsize=2**10)
def get_code_hash(code) -> str:
    """
    :param code: bytecode
    :return: Returns hash of the given bytecode
    """
    if type(code) == tuple:
        # Temporary hack, since we cannot find symbols of sha3
        return str(hash(code))

    code = code[2:] if code[:2] == "0x" else code
    try:
        hash_ = keccak(bytes.fromhex(code))
        return "0x" + hash_.hex()
    except ValueError:
        log.debug("Unable to change the bytecode to bytes. Bytecode: {}".format(code))
        return ""


def sha3(value):
    if type(value) == str:
        if value[:2] == "0x":
            new_hash = keccak(bytes.fromhex(value))
        else:
            new_hash = keccak(value.encode())
    else:
        new_hash = keccak(value)
    return new_hash


def zpad(x, l):
    """
    Left zero pad value `x` at least to length `l`.
    """
    return b"\x00" * max(0, l - len(x)) + x


def rzpad(value, total_length):
    """
    Right zero pad value `x` at least to length `l`.
    """
    return value + b"\x00" * max(0, total_length - len(value))
