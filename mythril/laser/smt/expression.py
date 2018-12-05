import z3


class Expression:
    """
    This is the base symbol type
    """
    def __init__(self, raw, annotations=None):
        self.raw = raw
        self._annotations = annotations or []

    @property
    def annotations(self):
        return self._annotations

    def annotate(self, annotation):
        if isinstance(annotation, list):
            self._annotations += annotation
        else:
            self._annotations.append(annotation)

    def simplify(self):
        """ Simplifies this expression """
        self.raw = z3.simplify(self.raw)


def simplify(expression: Expression):
    """ Simplifies the expression """
    expression.simplify()
