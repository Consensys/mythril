import hashlib

class Issue:

    def __init__(self, contract, function, pc, title, _type="Informational", description="", debug=""):

        self.title = title
        self.contract = contract
        self.function = function
        self.pc = pc
        self.description = description
        self.type = _type
        self.debug = debug
        self.code = None


    def as_dict(self):

        return {'title': self.title, 'description':self.description, 'type': self.type}


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

            if issue.code:
                text += "Affected code:\n\n" + issue.code + "\n--------------------\n"

            if len(issue.debug):
                text += "++++ Debugging info ++++\n" + issue.debug + "\n"

            text+="\n"

        return text
