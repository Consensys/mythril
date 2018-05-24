import hashlib
import json
from jinja2 import PackageLoader, Environment

class Issue:

    def __init__(self, contract, function, address, title, _type="Informational", description="", debug=""):

        self.title = title
        self.contract = contract
        self.function = function
        self.address = address
        self.description = description
        self.type = _type
        self.debug = debug
        self.filename = None
        self.code = None
        self.lineno = None

    def as_dict(self):

        issue = {'title': self.title, 'description':self.description, 'function': self.function, 'type': self.type, 'address': self.address, 'debug': self.debug}

        if self.filename and self.lineno:
            issue['filename'] = self.filename
            issue['lineno'] = self.lineno

        if self.code:
            issue['code'] = self.code

        return issue

    def add_code_info(self, contract):
        if self.address:
            codeinfo = contract.get_source_info(self.address)
            self.filename = codeinfo.filename
            self.code = codeinfo.code
            self.lineno = codeinfo.lineno

class Report:
    environment = Environment(loader=PackageLoader('mythril.analysis'))

    def __init__(self, verbose=False):
        self.issues = {}
        self.verbose = verbose
        pass

    def append_issue(self, issue):
        m = hashlib.md5()
        m.update((issue.contract + str(issue.address) + issue.title).encode('utf-8'))
        self.issues[m.digest()] = issue

    def as_text(self):
        filename = list(self.issues.values())[0].filename
        template = Report.environment.get_template('report_as_text.jinja2')
        return template.render(filename=filename, issues=self.issues, verbose=self.verbose)

    def as_json(self):
        issues = [issue.as_dict() for key, issue in self.issues.items()]
        result = {'success': True, 'error': None, 'issues': issues}
        return json.dumps(result)

    def as_markdown(self):
        filename = list(self.issues.values())[0].filename
        template = Report.environment.get_template('report_as_markdown.jinja2')
        return template.render(filename=filename, issues=self.issues, verbose=self.verbose)
