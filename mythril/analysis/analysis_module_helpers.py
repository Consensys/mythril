from typing import Callable
from mythril.laser.ethereum.state.annotation import StateAnnotation


def get_annotation(state, annotation_type: Callable) -> StateAnnotation:
    """
    Annotation is searched, if not found then a new annotation is created
    :param state: Get's annotation from state
    :param annotation_type: The type of the annotation
    :return: The annotation
    """
    annotations = list(state.get_annotations(annotation_type))
    if len(annotations) == 0:
        state.annotate(annotation_type())
        annotations = list(state.get_annotations(annotation_type))
    assert len(annotations) == 1
    return annotations[0]

