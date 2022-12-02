"""This module contains utility functions for the Mythril support package."""

from collections import OrderedDict
from copy import deepcopy
from eth_hash.auto import keccak
from functools import lru_cache
from typing import Dict
from z3 import is_true, simplify, And
import logging

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


class LRUCache:
    def __init__(self, size):
        self.size = size
        self.lru_cache = OrderedDict()

    def get(self, key):
        try:
            value = self.lru_cache.pop(key)
            self.lru_cache[key] = value
            return value
        except KeyError:
            return -1

    def put(self, key, value):
        try:
            self.lru_cache.pop(key)
        except KeyError:
            if len(self.lru_cache) >= self.size:
                self.lru_cache.popitem(last=False)
        self.lru_cache[key] = value


class ModelCache:
    def __init__(self):
        self.model_cache = LRUCache(size=100)

    @lru_cache(maxsize=2**10)
    def check_quick_sat(self, constraints) -> bool:
        model_list = list(reversed(self.model_cache.lru_cache.keys()))
        for model in reversed(self.model_cache.lru_cache.keys()):
            model_copy = deepcopy(model)
            if is_true(model_copy.eval(constraints, model_completion=True)):
                self.model_cache.put(model, self.model_cache.get(model) + 1)
                return model
        return False

    def put(self, key, value):
        self.model_cache.put(key, value)


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
