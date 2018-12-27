import logging
import json
import operator
from jinja2 import PackageLoader, Environment
import _pysha3 as sha3
import hashlib

from mythril.solidity.soliditycontract import SolidityContract
from mythril.analysis.swc_data import SWC_TO_TITLE
from mythril.support.source_support import Source


log = logging.getLogger(__name__)


class Issue:
    def __init__(
        self,
        contract,
        function_name,
        address,
        swc_id,
        title,
        bytecode,
        gas_used=(None, None),
        _type="Informational",
        description="",
        debug="",
    ):

        self.title = title
        self.contract = contract
        self.function = function_name
        self.address = address
        self.description = description
        self.type = _type
        self.debug = debug
        self.swc_id = swc_id
        self.min_gas_used, self.max_gas_used = gas_used
        self.filename = None
        self.code = None
        self.lineno = None
        self.source_mapping = None

        try:
            keccak = sha3.keccak_256()
            keccak.update(bytes.fromhex(bytecode))
            self.bytecode_hash = "0x" + keccak.hexdigest()
        except ValueError:
            log.debug(
                "Unable to change the bytecode to bytes. Bytecode: {}".format(bytecode)
            )
            self.bytecode_hash = ""

    @property
    def as_dict(self):

        issue = {
            "title": self.title,
            "swc-id": self.swc_id,
            "contract": self.contract,
            "description": self.description,
            "function": self.function,
            "type": self.type,
            "address": self.address,
            "debug": self.debug,
            "min_gas_used": self.min_gas_used,
            "max_gas_used": self.max_gas_used,
            "SourceMap": self.source_mapping,
        }

        if self.filename and self.lineno:
            issue["filename"] = self.filename
            issue["lineno"] = self.lineno

        if self.code:
            issue["code"] = self.code

        return issue

    def add_code_info(self, contract):
        if self.address and isinstance(self.contract, SolidityContract):
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
    environment = Environment(
        loader=PackageLoader("mythril.analysis"), trim_blocks=True
    )

    def __init__(self, verbose=False, source=Source()):
        self.issues = {}
        self.verbose = verbose
        self.solc_version = ""
        self.source_type = source.source_type
        self.source_format = source.source_format
        self.source_list = source.source_list
        self.meta = source.meta

    def sorted_issues(self):
        issue_list = [issue.as_dict for key, issue in self.issues.items()]
        return sorted(issue_list, key=operator.itemgetter("address", "title"))

    def append_issue(self, issue):
        m = hashlib.md5()
        m.update((issue.contract + str(issue.address) + issue.title).encode("utf-8"))
        self.issues[m.digest()] = issue

    def as_text(self):
        name = self._file_name()
        template = Report.environment.get_template("report_as_text.jinja2")
        return template.render(
            filename=name, issues=self.sorted_issues(), verbose=self.verbose
        )

    def as_json(self):
        result = {
            "issues": [
                {
                    "swcID": "SWC-{}".format(issue.swc_id),
                    "swcTitle": SWC_TO_TITLE[issue.swc_id],
                    "locations": [{"sourceMap": issue.source_mapping}],
                    "extra": "",
                }
                for issue in self.issues.values()
            ],
            "sourceType": self.source_type,
            "sourceFormat": self.source_format,
            "sourceList": self.source_list,
            "meta": self.meta,
        }
        return json.dumps(result, sort_keys=True)

    def as_swc_standard_format(self):
        """ Format defined for integration and correlation"""

        _issues = []
        sourceList = []

        for key, issue in self.issues.items():

            if issue.bytecode_hash not in sourceList:
                idx = len(sourceList)
                sourceList.append(issue.bytecode_hash)
            else:
                idx = sourceList.index(issue.bytecode_hash)

            try:
                title = SWC_TO_TITLE[issue.swc_id]
            except KeyError:
                title = "Unspecified Security Issue"

            _issues.append(
                {
                    "swcID": issue.swc_id,
                    "swcTitle": title,
                    "description": {
                        "head": "",
                        "tail": ""
                    },
                    "severity": issue.type,
                    "locations": [
                        {
                            "sourceMap": "%d:1:%d" % (issue.address, idx)
                        },
                    ],
                    "extra": {}
                }
            )

        result = {
            "issues": _issues,
            "sourceType": "raw-bytecode",
            "sourceFormat": "evm-byzantium-bytecode",
            "sourceList": sourceList,
            "meta": {}
        }

        return json.dumps(result, sort_keys=True)

    def as_markdown(self):
        filename = self._file_name()
        template = Report.environment.get_template("report_as_markdown.jinja2")
        return template.render(
            filename=filename, issues=self.sorted_issues(), verbose=self.verbose
        )

    def _file_name(self):
        if len(self.issues.values()) > 0:
            return list(self.issues.values())[0].filename
