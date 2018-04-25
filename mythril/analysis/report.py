import hashlib
import json
import attr
from jinja2 import PackageLoader, Environment


@attr.s
class Issue:
    contract = attr.ib()
    function = attr.ib()
    address = attr.ib()
    title = attr.ib()
    type = attr.ib(default="Informational")
    description = attr.ib(default="")
    debug = attr.ib(default="")
    filename = attr.ib(default=None)
    code = attr.ib(default=None)
    lineno = attr.ib(default=None)

    def add_code_info(self, contract):
        if self.address:
            codeinfo = contract.get_source_info(self.address)
            self.filename = codeinfo.filename
            self.code = codeinfo.code
            self.lineno = codeinfo.lineno

    def as_dict(self):
        return attr.asdict(self)


@attr.s
class Report(object):
    environment = Environment(loader=PackageLoader('mythril'))
    verbose = attr.ib(default=False)
    issues = attr.ib(init=False, default=attr.Factory(dict))

    def append_issue(self, issue):
        m = hashlib.md5()
        m.update((issue.contract + str(issue.address) + issue.title).encode('utf-8'))
        self.issues[m.digest()] = issue

    def as_json(self):
        return json.dumps({
            'success': True,
            'error': None,
            'issues': [issue.as_dict() for key, issue in self.issues.items()]
        })

    def as_text(self):
        template = Report.environment.get_template('report_as_text.jinja2')
        return template.render(issues=self.issues, verbose=self.verbose)

    def as_markdown(self):
        filename = list(self.issues.values())[0].filename
        template = Report.environment.get_template('report_as_markdown.jinja2')
        return template.render(filename=filename, issues=self.issues, verbose=self.verbose)
