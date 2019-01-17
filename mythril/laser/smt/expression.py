"""This module contains the SMT abstraction for a basic symbol expression."""

import z3


class Expression:
    """This is the base symbol class and maintains functionality for
    simplification and annotations."""

    def __init__(self, raw, annotations=None):
        """

        :param raw: 
        :param annotations: 
        """
        self.raw = raw
        self._annotations = annotations or []

    @property
    def annotations(self):
        """Gets the annotations for this expression.

        :return:
        """
        return self._annotations

    def annotate(self, annotation):
        """Annotates this expression with the given annotation.

        :param annotation:
        """
        if isinstance(annotation, list):
            self._annotations += annotation
        else:
            self._annotations.append(annotation)

    def simplify(self):
        """Simplify this expression."""
        self.raw = z3.simplify(self.raw)

    def __repr__(self):
        return repr(self.raw)


def simplify(expression: Expression):
    """Simplify the expression .

    :param expression:
    :return:
    """
    expression.simplify()
    return expression
