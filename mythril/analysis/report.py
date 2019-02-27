"""This module provides classes that make up an issue report."""
import logging
import json
import operator
from jinja2 import PackageLoader, Environment
import _pysha3 as sha3
import hashlib

from mythril.solidity.soliditycontract import SolidityContract
from mythril.analysis.swc_data import SWC_TO_TITLE
from mythril.support.source_support import Source
from mythril.start_time import StartTime
from time import time

log = logging.getLogger(__name__)


class Issue:
    """Representation of an issue and its location."""

    def __init__(
        self,
        contract,
        function_name,
        address,
        swc_id,
        title,
        bytecode,
        gas_used=(None, None),
        severity=None,
        description_head="",
        description_tail="",
        debug="",
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
        :param debug: The transaction sequence
        """
        self.title = title
        self.contract = contract
        self.function = function_name
        self.address = address
        self.description_head = description_head
        self.description_tail = description_tail
        self.description = "%s\n%s" % (description_head, description_tail)
        self.severity = severity
        self.debug = debug
        self.swc_id = swc_id
        self.min_gas_used, self.max_gas_used = gas_used
        self.filename = None
        self.code = None
        self.lineno = None
        self.source_mapping = None
        self.discovery_time = time() - StartTime().global_start_time

        try:
            keccak = sha3.keccak_256()
            keccak.update(
                bytes.fromhex(bytecode[2:])
                if bytecode[:2] == "0x"
                else bytes.fromhex(bytecode)
            )
            self.bytecode_hash = "0x" + keccak.hexdigest()
        except ValueError:
            log.debug(
                "Unable to change the bytecode to bytes. Bytecode: {}".format(bytecode)
            )
            self.bytecode_hash = ""

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
            "debug": self.debug,
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

    def add_code_info(self, contract):
        """

        :param contract:
        """
        if self.address and isinstance(contract, SolidityContract):
            codeinfo = contract.get_source_info(
                self.address, constructor=(self.function == "constructor")
            )
            self.filename = codeinfo.filename
            self.code = codeinfo.code
            self.lineno = codeinfo.lineno
            self.source_mapping = codeinfo.solc_mapping
        else:
            self.source_mapping = self.address


class Report:
    """A report containing the content of multiple issues."""

    environment = Environment(
        loader=PackageLoader("mythril.analysis"), trim_blocks=True
    )

    def __init__(self, verbose=False, source=None):
        """

        :param verbose:
        """
        self.issues = {}
        self.verbose = verbose
        self.solc_version = ""
        self.meta = {}
        self.source = source or Source()

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
        m.update((issue.contract + str(issue.address) + issue.title).encode("utf-8"))
        self.issues[m.digest()] = issue

    def as_text(self):
        """

        :return:
        """
        name = self._file_name()
        template = Report.environment.get_template("report_as_text.jinja2")
        return template.render(
            filename=name, issues=self.sorted_issues(), verbose=self.verbose
        )

    def as_json(self):
        """

        :return:
        """
        result = {"success": True, "error": None, "issues": self.sorted_issues()}
        return json.dumps(result, sort_keys=True)

    def as_swc_standard_format(self):
        """Format defined for integration and correlation.

        :return:
        """
        _issues = []
        source_list = []

        for key, issue in self.issues.items():

            if issue.bytecode_hash not in source_list:
                idx = len(source_list)
                source_list.append(issue.bytecode_hash)
            else:
                idx = source_list.index(issue.bytecode_hash)

            try:
                title = SWC_TO_TITLE[issue.swc_id]
            except KeyError:
                title = "Unspecified Security Issue"

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
                    "extra": {},
                }
            )

        result = [
            {
                "issues": _issues,
                "sourceType": "raw-bytecode",
                "sourceFormat": "evm-byzantium-bytecode",
                "sourceList": source_list,
                "meta": {},
            }
        ]

        return json.dumps(result, sort_keys=True)

    def as_markdown(self):
        """

        :return:
        """
        filename = self._file_name()
        template = Report.environment.get_template("report_as_markdown.jinja2")
        return template.render(
            filename=filename, issues=self.sorted_issues(), verbose=self.verbose
        )

    def _file_name(self):
        """

        :return:
        """
        if len(self.issues.values()) > 0:
            return list(self.issues.values())[0].filename
