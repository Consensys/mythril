"""This module contains functionality used to easily analyse Truffle
projects."""
import json
import logging
import os
import re
import sys
import warnings
import shutil
import subprocess
from pathlib import Path
from typing import TYPE_CHECKING, List


from mythril.analysis.report import Report
from mythril.analysis.security import fire_lasers
from mythril.analysis.symbolic import SymExecWrapper
from mythril.ethereum import util
from mythril.ethereum.evmcontract import EVMContract
from mythril.laser.ethereum.util import get_instruction_index
from mythril.solidity.soliditycontract import SourceMapping

log = logging.getLogger(__name__)


def format_Warning(message, category, filename, lineno, line=""):
    return "{}: {}\n\n".format(str(filename), str(message))


warnings.formatwarning = format_Warning


def analyze_foundry_project(args):
    """

    :param sigs:
    :param args:
    """

    project_root = os.getcwd()

    cmd = ["forge", "build", "--build-info", "--force"]

    with subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=project_root,
        executable=shutil.which(cmd[0]),
    ) as p:

        stdout, stderr = p.communicate()
        stdout, stderr = (stdout.decode(), stderr.decode())
        if stderr:
            log.error(stderr)

        build_dir = Path(project_root, "artifacts", "contracts", "build-info")

    build_dir = os.path.join(project_root, "artifacts", "contracts", "build-info")

    files = os.listdir(build_dir)

    files = sorted(
        os.listdir(build_dir), key=lambda x: os.path.getmtime(Path(build_dir, x))
    )
    print(files)
    files = [str(f) for f in files if str(f).endswith(".json")]
    if not files:
        txt = f"`compile` failed. Can you run it?\n{build_dir} is empty"
        raise InvalidCompilation(txt)

    for file in files:
        build_info = Path(build_dir, file)

        uniq_id = file if ".json" not in file else file[0:-5]

        with open(build_info, encoding="utf8") as file_desc:
            loaded_json = json.load(file_desc)

            targets_json = loaded_json["output"]

            version_from_config = loaded_json["solcVersion"]
            input_json = loaded_json["input"]
            compiler = "solc" if input_json["language"] == "Solidity" else "vyper"
            optimizer = input_json["settings"]["optimizer"]["enabled"]

            if "contracts" in targets_json:
                for original_filename, contracts_info in targets_json[
                    "contracts"
                ].items():

                    print(original_filename)

                    for contract_name, info in contracts_info.items():

                        source_unit.contracts_names.add(contract_name)
                        source_unit.abis[contract_name] = info["abi"]
                        source_unit.bytecodes_init[contract_name] = info["evm"][
                            "bytecode"
                        ]["object"]
                        source_unit.bytecodes_runtime[contract_name] = info["evm"][
                            "deployedBytecode"
                        ]["object"]
                        source_unit.srcmaps_init[contract_name] = info["evm"][
                            "bytecode"
                        ]["sourceMap"].split(";")
                        source_unit.srcmaps_runtime[contract_name] = info["evm"][
                            "deployedBytecode"
                        ]["sourceMap"].split(";")
                        userdoc = info.get("userdoc", {})
                        devdoc = info.get("devdoc", {})
                        natspec = Natspec(userdoc, devdoc)
                        source_unit.natspec[contract_name] = natspec

            if "sources" in targets_json:
                for path, info in targets_json["sources"].items():
                    if skip_filename:
                        path = convert_filename(
                            target,
                            relative_to_short,
                            crytic_compile,
                            working_dir=working_dir,
                        )
                    else:
                        path = convert_filename(
                            path,
                            relative_to_short,
                            crytic_compile,
                            working_dir=working_dir,
                        )

                    source_unit = compilation_unit.create_source_unit(path)
                    source_unit.ast = info["ast"]
