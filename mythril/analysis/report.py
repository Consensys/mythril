"""This module provides classes that make up an issue report."""
import logging
import re
import json
import operator

try:
    from eth_abi import decode
except ImportError:
    from eth_abi import decode_abi as decode

from jinja2 import PackageLoader, Environment
from typing import Dict, List, Any, Optional
import hashlib

from mythril.laser.execution_info import ExecutionInfo
from mythril.solidity.soliditycontract import SolidityContract
from mythril.analysis.swc_data import SWC_TO_TITLE
from mythril.support.source_support import Source
from mythril.support.start_time import StartTime
from mythril.support.support_utils import get_code_hash
from mythril.support.signatures import SignatureDB
from time import time

log = logging.getLogger(__name__)


class Issue:
    """Representation of an issue and its location."""

    def __init__(
        self,
        contract: str,
        function_name: str,
        address: int,
        swc_id: str,
        title: str,
        bytecode: str,
        gas_used=(None, None),
        severity=None,
        description_head="",
        description_tail="",
        transaction_sequence=None,
        source_location=None,
    ):
        """

        :param contract: The contract
        :param function_name: Function name where the issue is detected
        :param address: The address of the issue
        :param swc_id: Issue's corresponding swc-id
        :param title: Title
        :param bytecode: bytecode of the issue
        :param gas_used: amount of gas used
        :param severity: The severity of the issue
        :param description_head: The top part of description
        :param description_tail: The bottom part of the description
        :param transaction_sequence: The transaction sequence
        """
        self.title = title
        self.contract = contract
        self.function = function_name
        self.address = address
        self.description_head = description_head
        self.description_tail = description_tail
        self.description = "%s\n%s" % (description_head, description_tail)
        self.severity = severity
        self.swc_id = swc_id
        self.min_gas_used, self.max_gas_used = gas_used
        self.filename = None
        self.code = None
        self.lineno = None
        self.source_mapping = None
        self.discovery_time = time() - StartTime().global_start_time
        self.bytecode_hash = get_code_hash(bytecode)
        self.transaction_sequence = transaction_sequence
        self.source_location = source_location

    @property
    def transaction_sequence_users(self):
        """Returns the transaction sequence without pre-generated block data"""
        return self.transaction_sequence

    @property
    def transaction_sequence_jsonv2(self):
        """Returns the transaction sequence as a json string with pre-generated block data"""
        return (
            self.add_block_data(self.transaction_sequence)
            if self.transaction_sequence
            else None
        )

    @staticmethod
    def add_block_data(transaction_sequence: Dict):
        """Adds sane block data to a transaction_sequence"""
        for step in transaction_sequence["steps"]:
            step["gasLimit"] = "0x7d000"
            step["gasPrice"] = "0x773594000"
            step["blockCoinbase"] = "0xcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcbcb"
            step["blockDifficulty"] = "0xa7d7343662e26"
            step["blockGasLimit"] = "0x7d0000"
            step["blockNumber"] = "0x66e393"
            step["blockTime"] = "0x5bfa4639"
        return transaction_sequence

    @property
    def as_dict(self):
        """

        :return:
        """

        issue = {
            "title": self.title,
            "swc-id": self.swc_id,
            "contract": self.contract,
            "description": self.description,
            "function": self.function,
            "severity": self.severity,
            "address": self.address,
            "tx_sequence": self.transaction_sequence,
            "min_gas_used": self.min_gas_used,
            "max_gas_used": self.max_gas_used,
            "sourceMap": self.source_mapping,
        }

        if self.filename and self.lineno:
            issue["filename"] = self.filename
            issue["lineno"] = self.lineno

        if self.code:
            issue["code"] = self.code

        return issue

    def _set_internal_compiler_error(self):
        """
        Adds the false positive to description and changes severity to low
        """
        self.severity = "Low"
        self.description_tail += (
            " This issue is reported for internal compiler generated code."
        )
        self.description = "%s\n%s" % (self.description_head, self.description_tail)
        self.code = ""

    def add_code_info(self, contract):
        """

        :param contract:
        """
        if self.address and isinstance(contract, SolidityContract):
            is_constructor = False
            if self.function == "constructor":
                is_constructor = True

            if self.source_location:
                codeinfo = contract.get_source_info(
                    self.source_location, constructor=is_constructor
                )
            else:
                codeinfo = contract.get_source_info(
                    self.address, constructor=is_constructor
                )

            if codeinfo is None:
                self.source_mapping = self.address
                self.filename = "Internal File"
                return

            self.filename = codeinfo.filename
            self.code = codeinfo.code
            self.lineno = codeinfo.lineno
            if self.lineno is None:
                self._set_internal_compiler_error()
            self.source_mapping = codeinfo.solc_mapping
        else:
            self.source_mapping = self.address

    @staticmethod
    def decode_bytes(val):
        if isinstance(val, bytes):
            return val.decode()
        elif isinstance(val, list) or isinstance(val, tuple):
            return [Issue.decode_bytes(x) for x in val]
        else:
            return val

    def resolve_function_names(self):
        """Resolves function names for each step"""

        if (
            self.transaction_sequence is None
            or "steps" not in self.transaction_sequence
        ):
            return

        signatures = SignatureDB()

        for step in self.transaction_sequence["steps"]:
            _hash = step["input"][:10]

            try:
                sig = signatures.get(_hash)
                # TODO: Check other mythx tools for dependency before supporting multiple possible function names
                if len(sig) > 0:
                    step["name"] = sig[0]
                    step["resolved_input"] = Issue.resolve_input(
                        step["calldata"], sig[0]
                    )
                    if step["resolved_input"] is not None:
                        step["resolved_input"] = list(step["resolved_input"])
                        for i, val in enumerate(step["resolved_input"]):
                            step["resolved_input"][i] = Issue.decode_bytes(val)

                        step["resolved_input"] = tuple(step["resolved_input"])

                else:
                    step["name"] = "unknown"
            except ValueError:
                step["name"] = "unknown"

    @staticmethod
    def resolve_input(data, function_name):
        """
        Adds decoded calldate to the tx sequence.
        """
        data = data[10:]

        # Eliminates the first and last brackets
        # Since signature such as func((bytes32,bytes32,uint8)[],(address[],uint32)) are valid
        type_info = function_name[function_name.find("(") + 1 : -1]
        type_info = re.split(r",\s*(?![^()]*\))", type_info)

        if len(data) % 64 > 0:
            data += "0" * (64 - len(data) % 64)
        try:
            decoded_output = decode(type_info, bytes.fromhex(data))
            return decoded_output
        except Exception as e:
            return None


class Report:
    """A report containing the content of multiple issues."""

    environment = Environment(
        loader=PackageLoader("mythril.analysis"), trim_blocks=True
    )

    def __init__(
        self,
        contracts=None,
        exceptions=None,
        execution_info: Optional[List[ExecutionInfo]] = None,
    ):
        """

        :param contracts:
        :param exceptions:
        """
        self.issues: Dict[bytes, Issue] = {}
        self.solc_version = ""
        self.meta: Dict[str, Any] = {}
        self.source = Source()
        self.source.get_source_from_contracts_list(contracts)
        self.exceptions = exceptions or []
        self.execution_info = execution_info or []

    def sorted_issues(self):
        """

        :return:
        """
        issue_list = [issue.as_dict for key, issue in self.issues.items()]
        return sorted(issue_list, key=operator.itemgetter("address", "title"))

    def append_issue(self, issue):
        """

        :param issue:
        """
        m = hashlib.md5()
        m.update(
            (issue.contract + issue.function + str(issue.address) + issue.title).encode(
                "utf-8"
            )
        )
        issue.resolve_function_names()
        self.issues[m.digest()] = issue

    def as_text(self):
        """

        :return:
        """
        name = self._file_name()
        template = Report.environment.get_template("report_as_text.jinja2")

        return template.render(filename=name, issues=self.sorted_issues())

    def as_json(self):
        """

        :return:
        """
        result = {"success": True, "error": None, "issues": self.sorted_issues()}

        return json.dumps(result, sort_keys=True)

    def _get_exception_data(self) -> dict:
        if not self.exceptions:
            return {}
        logs: List[Dict] = []
        for exception in self.exceptions:
            logs += [{"level": "error", "hidden": True, "msg": exception}]
        return {"logs": logs}

    def as_swc_standard_format(self):
        """Format defined for integration and correlation.

        :return:
        """
        # Setup issues
        _issues = []

        for _, issue in self.issues.items():

            idx = self.source.get_source_index(issue.bytecode_hash)
            try:
                title = SWC_TO_TITLE[issue.swc_id]
            except KeyError:
                title = "Unspecified Security Issue"
            extra = {"discoveryTime": int(issue.discovery_time * 10**9)}
            if issue.transaction_sequence_jsonv2:
                extra["testCases"] = [issue.transaction_sequence_jsonv2]

            _issues.append(
                {
                    "swcID": "SWC-" + issue.swc_id,
                    "swcTitle": title,
                    "description": {
                        "head": issue.description_head,
                        "tail": issue.description_tail,
                    },
                    "severity": issue.severity,
                    "locations": [{"sourceMap": "%d:1:%d" % (issue.address, idx)}],
                    "extra": extra,
                }
            )
        # Setup meta
        meta_data = self.meta

        # Add logs to meta
        meta_data.update(self._get_exception_data())

        # Add execution info to meta
        analysis_duration = int(
            round((time() - StartTime().global_start_time) * (10**9))
        )
        meta_data["mythril_execution_info"] = {"analysis_duration": analysis_duration}
        for execution_info in self.execution_info:
            meta_data["mythril_execution_info"].update(execution_info.as_dict())

        result = [
            {
                "issues": _issues,
                "sourceType": self.source.source_type,
                "sourceFormat": self.source.source_format,
                "sourceList": self.source.source_list,
                "meta": meta_data,
            }
        ]

        return json.dumps(result, sort_keys=True)

    def as_markdown(self):
        """

        :return:
        """
        filename = self._file_name()
        template = Report.environment.get_template("report_as_markdown.jinja2")
        return template.render(filename=filename, issues=self.sorted_issues())

    def _file_name(self):
        """

        :return:
        """
        if len(self.issues.values()) > 0:
            return list(self.issues.values())[0].filename
