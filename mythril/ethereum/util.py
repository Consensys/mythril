"""This module contains various utility functions regarding unit conversion and
solc integration."""
import binascii
import json
import sys
import os
import platform
import logging
import solc
import re

from pathlib import Path
from requests.exceptions import ConnectionError
from subprocess import PIPE, Popen
from typing import Optional

from json.decoder import JSONDecodeError
from semantic_version import Version, NpmSpec

from mythril.exceptions import CompilerError
from mythril.support.support_args import args

import solcx

log = logging.getLogger(__name__)


def safe_decode(hex_encoded_string):
    """

    :param hex_encoded_string:
    :return:
    """
    if hex_encoded_string.startswith("0x"):
        return bytes.fromhex(hex_encoded_string[2:])
    else:
        return bytes.fromhex(hex_encoded_string)


def get_solc_json(file, solc_binary="solc", solc_settings_json=None):
    """

    :param file:
    :param solc_binary:
    :param solc_settings_json:
    :return:
    """
    if args.solc_args is None:
        cmd = [solc_binary, "--standard-json", "--allow-paths", ".,/"]
    else:
        cmd = [solc_binary, "--standard-json"] + args.solc_args.split()

    settings = {}
    if solc_settings_json:
        with open(solc_settings_json) as f:
            settings = json.load(f)
    if "optimizer" not in settings:
        settings.update({"optimizer": {"enabled": False}})

    settings.update(
        {
            "outputSelection": {
                "*": {
                    "": ["ast"],
                    "*": [
                        "metadata",
                        "evm.bytecode",
                        "evm.deployedBytecode",
                        "evm.methodIdentifiers",
                    ],
                }
            },
        }
    )

    input_json = json.dumps(
        {
            "language": "Solidity",
            "sources": {file: {"urls": [file]}},
            "settings": settings,
        }
    )

    try:
        p = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE)
        stdout, stderr = p.communicate(bytes(input_json, "utf8"))

    except FileNotFoundError:
        raise CompilerError(
            "Compiler not found. Make sure that solc is installed and in PATH, or set the SOLC environment variable."
        )

    out = stdout.decode("UTF-8")

    try:
        result = json.loads(out)
    except JSONDecodeError as e:
        log.error(f"Encountered a decode error.\n stdout:{out}\n stderr: {stderr}")
        raise e

    for error in result.get("errors", []):
        if error["severity"] == "error":
            raise CompilerError(
                "Solc experienced a fatal error.\n\n%s" % error["formattedMessage"]
            )

    return result


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

    default_binary = "/usr/bin/solc"
    if platform.system() == "Darwin":
        solcx.import_installed_solc()
    solcx.install_solc("v" + version)
    solcx.set_solc_version("v" + version)
    solc_binary = solcx.install.get_executable()
    return solc_binary


try:
    all_versions = solcx.get_installable_solc_versions()
except ConnectionError:
    # No internet, trying to proceed with installed compilers
    all_versions = solcx.get_installed_solc_versions()


def extract_version(file: str) -> Optional[str]:
    version_line = None
    for line in file.split("\n"):
        if "pragma solidity" not in line:
            continue
        version_line = line.rstrip()
        break
    if version_line is None:
        return None

    assert "pragma solidity" in version_line
    if version_line[-1] == ";":
        version_line = version_line[:-1]
    version_line = version_line.split(";")[0]
    version = re.search("pragma solidity ([\d.^]*)", version_line).group(1)

    version_constraint = NpmSpec(version)
    for version in all_versions:
        if version in version_constraint:
            return str(version)
    return None


def extract_binary(file: str) -> str:
    with open(file) as f:
        version = extract_version(f.read())
    if version and NpmSpec("^0.8.0").match(Version(version)):
        args.use_integer_module = False

    if version is None:
        return os.environ.get("SOLC") or "solc"
    return solc_exists(version)
