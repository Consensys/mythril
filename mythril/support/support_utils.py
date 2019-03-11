"""This module contains utility functions for the Mythril support package."""
from typing import Dict
import logging
import _pysha3 as sha3

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


def get_code_hash(code):
    """
    :param code: bytecode
    :return: Returns hash of the given bytecode
    """
    try:
        keccak = sha3.keccak_256()
        keccak.update(bytes.fromhex(code[2:]))
        return "0x" + keccak.hexdigest()
    except ValueError:
        log.debug("Unable to change the bytecode to bytes. Bytecode: {}".format(code))
        return ""
