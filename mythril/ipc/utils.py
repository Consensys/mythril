import os
import sys

from .constants import BLOCK_TAGS


def hex_to_dec(x):
    '''
    Convert hex to decimal
    '''
    return int(x, 16)

def to_bytes(text):
    return text.encode('utf-8')

def to_text(byte_array):
    return byte_array.decode('utf-8')

def clean_hex(d):
    '''
    Convert decimal to hex and remove the "L" suffix that is appended to large
    numbers
    '''
    return hex(d).rstrip('L')

def validate_block(block):
    if isinstance(block, str):
        if block not in BLOCK_TAGS:
            raise ValueError('invalid block tag')
    if isinstance(block, int):
        block = hex(block)
    return block


def wei_to_ether(wei):
    '''
    Convert wei to ether
    '''
    return 1.0 * wei / 10**18


def ether_to_wei(ether):
    '''
    Convert ether to wei
    '''
    return ether * 10**18


def get_default_ipc_path(testnet=False):
    if testnet:
        testnet = "testnet"
    else:
        testnet = ""

    if sys.platform == 'darwin':
        ipc_path = os.path.expanduser(os.path.join("~", "Library", "Ethereum", testnet, "geth.ipc"))
        if os.path.exists(ipc_path):
            return ipc_path

        ipc_path = os.path.expanduser(os.path.join("~", "Library", "Application Support", "io.parity.ethereum", "jsonrpc.ipc"))
        if os.path.exists(ipc_path):
            return ipc_path

    elif sys.platform.startswith('linux'):
        ipc_path = os.path.expanduser(os.path.join("~", ".ethereum", testnet, "geth.ipc"))
        if os.path.exists(ipc_path):
            return ipc_path

        ipc_path = os.path.expanduser(os.path.join("~", ".local", "share", "io.parity.ethereum", "jsonrpc.ipc"))
        if os.path.exists(ipc_path):
            return ipc_path

    elif sys.platform == 'win32':
        ipc_path = os.path.join("\\\\", ".", "pipe", "geth.ipc")
        if os.path.exists(ipc_path):
            return ipc_path

        ipc_path = os.path.join("\\\\", ".", "pipe", "jsonrpc.ipc")
        if os.path.exists(ipc_path):
            return ipc_path

    else:
        raise ValueError(
            "Unsupported platform '{0}'.  Only darwin/linux2/win32 are "
            "supported.  You must specify the ipc_path".format(sys.platform)
        )