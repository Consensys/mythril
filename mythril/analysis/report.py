class Issue:

    def __init__(self, contract, function, pc, title, _type="Informational", description="", debug=""):

        self.title = title
        self.contract = contract
        self.function = function
        self.pc = pc
        self.description = description
        self.type = _type
        self.debug = debug


    def as_dict(self):

        return {'title': self.title, 'description':self.description, 'type': self.type}


class Report:

    def __init__(self, issues = []):
        self.issues = issues


    def as_text(self):
        text = ""

        for issue in self.issues:
            text += "==== " + issue.title + " ====\n"
            text += "Type: " + issue.type + "\n"

            if len(issue.contract):
                text += "Contract: " + issue.contract + "\n" 
            else:
                text += "Contract: Unknown\n"              

            text += "Function name: " + issue.function + "\n"
            text += "PC address: " + str(issue.pc) + "\n"

            text += "--------------------\n" + issue.description + "\n"
            text += "++++ Debugging info ++++\n" + issue.debug + "\n"


        return text

