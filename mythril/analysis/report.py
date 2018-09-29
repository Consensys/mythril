import hashlib
import json
import operator
from jinja2 import PackageLoader, Environment


class Issue:

    def __init__(self, contract, function, address, swc_id, title, _type="Informational", description="", debug=""):

        self.title = title
        self.contract = contract
        self.function = function
        self.address = address
        self.description = description
        self.type = _type
        self.debug = debug
        self.swc_id = swc_id
        self.filename = None
        self.code = None
        self.lineno = None


    @property
    def as_dict(self):

        issue = {'title': self.title, 'swc_id': self.swc_id, 'contract': self.contract, 'description': self.description,
                 'function': self.function, 'type': self.type, 'address': self.address, 'debug': self.debug}

        if self.filename and self.lineno:
            issue['filename'] = self.filename
            issue['lineno'] = self.lineno

        if self.code:
            issue['code'] = self.code

        return issue

    def add_code_info(self, contract):
        if self.address:
            codeinfo = contract.get_source_info(self.address, constructor=(self.function == 'constructor'))
            self.filename = codeinfo.filename
            self.code = codeinfo.code
            self.lineno = codeinfo.lineno


class Report:
    environment = Environment(loader=PackageLoader('mythril.analysis'), trim_blocks=True)

    def __init__(self, verbose=False):
        self.issues = {}
        self.verbose = verbose
        pass

    def sorted_issues(self):
        issue_list = [issue.as_dict for key, issue in self.issues.items()]
        return sorted(issue_list, key=operator.itemgetter('address', 'title'))

    def append_issue(self, issue):
        m = hashlib.md5()
        m.update((issue.contract + str(issue.address) + issue.title).encode('utf-8'))
        self.issues[m.digest()] = issue

    def as_text(self):
        name = self._file_name()
        template = Report.environment.get_template('report_as_text.jinja2')
        return template.render(filename=name, issues=self.sorted_issues(), verbose=self.verbose)

    def as_json(self):
        result = {'success': True, 'error': None, 'issues': self.sorted_issues()}
        return json.dumps(result, sort_keys=True)

    def as_markdown(self):
        filename = self._file_name()
        template = Report.environment.get_template('report_as_markdown.jinja2')
        return template.render(filename=filename, issues=self.sorted_issues(), verbose=self.verbose)

    def _file_name(self):
        if len(self.issues.values()) > 0:
            return list(self.issues.values())[0].filename
