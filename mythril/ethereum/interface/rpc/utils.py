"""This module contains various utility functions regarding the RPC data format
and validation."""
from .constants import BLOCK_TAGS


def hex_to_dec(x):
    """Convert hex to decimal.

    :param x:
    :return:
    """
    return int(x, 16)


def clean_hex(d):
    """Convert decimal to hex and remove the "L" suffix that is appended to
    large numbers.

    :param d:
    :return:
    """
    return hex(d).rstrip("L")


def validate_block(block):
    """

    :param block:
    :return:
    """
    if isinstance(block, str):
        if block not in BLOCK_TAGS:
            raise ValueError("invalid block tag")
    if isinstance(block, int):
        block = hex(block)
    return block


def wei_to_ether(wei):
    """Convert wei to ether.

    :param wei:
    :return:
    """
    return 1.0 * wei / 10 ** 18


def ether_to_wei(ether):
    """Convert ether to wei.

    :param ether:
    :return:
    """
    return ether * 10 ** 18
