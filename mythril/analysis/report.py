class Issue:

    def __init__(self, title, _type = "Informational", description = ""):

        self.title = title
        self.description = description
        self.type = _type


    def as_dict(self):

        return {'title': self.title, 'description':self.description, 'type': self.type}


class Report:

    def __init__(self, issues = []):
        self.issues = issues


    def as_text(self):
        text = ""

        for issue in self.issues:
            text += "=== " + issue.title + " ===\n"
            text += "Type: " + issue.type + "\n"
            text += issue.description + "\n"

        return text

