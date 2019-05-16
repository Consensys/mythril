"""This module contains various utility functions regarding unit conversion and
solc integration."""
import binascii
import json
import os
from pathlib import Path
from subprocess import PIPE, Popen

from ethereum.abi import encode_abi, encode_int, method_id
from ethereum.utils import zpad

from mythril.exceptions import CompilerError


def safe_decode(hex_encoded_string):
    """

    :param hex_encoded_string:
    :return:
    """
    if hex_encoded_string.startswith("0x"):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def get_solc_json(file, solc_binary="solc", solc_args=None):
    """

    :param file:
    :param solc_binary:
    :param solc_args:
    :return:
    """

    cmd = [solc_binary, "--combined-json", "bin,bin-runtime,srcmap,srcmap-runtime,ast"]

    if solc_args:
        cmd.extend(solc_args.split())
    if not "--allow-paths" in cmd:
        cmd.extend(["--allow-paths", "."])
    else:
        for i, arg in enumerate(cmd):
            if arg == "--allow-paths":
                cmd[i + 1] += ",."

    cmd.append(file)

    try:
        p = Popen(cmd, stdout=PIPE, stderr=PIPE)

        stdout, stderr = p.communicate()
        ret = p.returncode

        if ret != 0:
            raise CompilerError(
                "Solc experienced a fatal error (code %d).\n\n%s"
                % (ret, stderr.decode("UTF-8"))
            )
    except FileNotFoundError:
        raise CompilerError(
            "Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable."
        )

    out = stdout.decode("UTF-8")

    if not len(out):
        raise CompilerError("Compilation failed.")

    return json.loads(out)


def encode_calldata(func_name, arg_types, args):
    """

    :param func_name:
    :param arg_types:
    :param args:
    :return:
    """
    mid = method_id(func_name, arg_types)
    function_selector = zpad(encode_int(mid), 4)
    args = encode_abi(arg_types, args)
    return "0x" + function_selector.hex() + args.hex()


def get_random_address():
    """

    :return:
    """
    return binascii.b2a_hex(os.urandom(20)).decode("UTF-8")


def get_indexed_address(index):
    """

    :param index:
    :return:
    """
    return "0x" + (hex(index)[2:] * 40)


def solc_exists(version):
    """

    :param version:
    :return:
    """
    solc_binaries = [
        os.path.join(
            os.environ.get("HOME", str(Path.home())),
            ".py-solc/solc-v" + version,
            "bin/solc",
        )  # py-solc setup
    ]
    if version.startswith("0.5"):
        # Temporary fix to support v0.5.x with Ubuntu PPA setup
        solc_binaries.append("/usr/bin/solc")
    for solc_path in solc_binaries:
        if os.path.exists(solc_path):
            return solc_path
