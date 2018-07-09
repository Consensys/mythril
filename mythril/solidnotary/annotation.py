from re import search

class Annotation:

    def __init__(self, annstring, lineno, fileoffset):
        self.annstring = annstring

        annotation = search(r'@(?P<aname>[^\{\}]*)(\{(?P<acontent>.*)\})?', annstring)
        if not annotation:
            raise SyntaxError("{} is not a correct annotation".format(annstring))

        self.aname = annotation['aname']
        self.acontent = annotation['acontent']
        self.lineno = lineno
        self.length = len(annstring)
        self.fileoffset = fileoffset

class ContractAnnotation(Annotation):
    pass

class MemberAnnotation(Annotation):
    pass

class InlineAnnotation(Annotation):
    pass

class ContractAnnotation(Annotation):
    pass
