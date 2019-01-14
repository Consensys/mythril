"""This module contains the SMT abstraction for a basic symbol expression."""
from typing import Optional, List, Any, TypeVar, Generic, cast
import z3


Annotations = List[Any]
T = TypeVar("T", bound=z3.ExprRef)


class Expression(Generic[T]):
    """This is the base symbol class and maintains functionality for
    simplification and annotations."""

    def __init__(self, raw: T, annotations: Optional[Annotations] = None):
        """

        :param raw: 
        :param annotations: 
        """
        self.raw = raw
        self._annotations = annotations or []

    @property
    def annotations(self) -> Annotations:
        """Gets the annotations for this expression.

        :return:
        """
        return self._annotations

    def annotate(self, annotation: Any) -> None:
        """Annotates this expression with the given annotation.

        :param annotation:
        """
        if isinstance(annotation, list):
            self._annotations += annotation
        else:
            self._annotations.append(annotation)

    def simplify(self) -> None:
        """Simplify this expression."""
        self.raw = cast(T, z3.simplify(self.raw))

    def __repr__(self) -> str:
        return repr(self.raw)


def simplify(expression: Expression) -> Expression:
    """Simplify the expression .

    :param expression:
    :return:
    """
    expression.simplify()
    return expression
