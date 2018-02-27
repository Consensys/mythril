import hashlib
import json

class Issue:

    def __init__(self, contract, function, pc, title, _type="Informational", description="", debug=""):

        self.title = title
        self.contract = contract
        self.function = function
        self.pc = pc
        self.description = description
        self.type = _type
        self.debug = debug
        self.filename = None
        self.code = None
        self.lineno = None


    def as_dict(self):

        issue = {'title': self.title, 'description':self.description, 'function': self.function, 'type': self.type, 'address': self.pc, 'debug': self.debug}

        if self.filename and self.lineno:
            issue['filename'] = self.filename 
            issue['lineno'] = self.lineno

        if self.code:
            issue['code'] = self.code

        return issue


class Report:

    def __init__(self):
        self.issues = {}
        pass

    def append_issue(self, issue):
        m = hashlib.md5()
        m.update((issue.contract + str(issue.pc) + issue.title).encode('utf-8'))
        self.issues[m.digest()] = issue

    def as_text(self):
        text = ""

        for key, issue in self.issues.items():

            text += "==== " + issue.title + " ====\n"
            text += "Type: " + issue.type + "\n"

            if len(issue.contract):
                text += "Contract: " + issue.contract + "\n" 
            else:
                text += "Contract: Unknown\n"              

            text += "Function name: " + issue.function + "\n"
            text += "PC address: " + str(issue.pc) + "\n"

            text += issue.description + "\n--------------------\n"

            if issue.filename and issue.lineno:
                 text += "In file: " + issue.filename + ":" + str(issue.lineno)    

            if issue.code:
                text += "\n\n" + issue.code + "\n\n--------------------\n"

            text+="\n"

        return text


    def as_json(self):
        issues = []

        for key, issue in self.issues.items():

            issues.append(issue.as_dict())

        return json.dumps(issues)


    def as_markdown(self):
        text = "# Analysis Results\n"

        for key, issue in self.issues.items():

            text += "## " + issue.title + "\n"
            text += "- Type: " + issue.type + "\n"

            if len(issue.contract):
                text += "- Contract: " + issue.contract + "\n" 
            else:
                text += "- Contract: Unknown\n"              

            text += "- Function name: " + issue.function + "\n"
            text += "- PC address: " + str(issue.pc) + "\n\n"

            text += "### Description\n" + issue.description + "\n"

            if issue.filename and issue.lineno:
                text += "\nIn *%s:*\n%d" % (issue.filename, issue.lineno)

            if issue.code:
                text += "\n```\n" + issue.code + "\n```\n"

        return text
