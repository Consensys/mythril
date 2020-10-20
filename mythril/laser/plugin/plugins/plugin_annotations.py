from mythril.laser.ethereum.state.annotation import (
    StateAnnotation,
    MergeableStateAnnotation,
)

from copy import copy
from typing import Dict, List, Set
import logging

log = logging.getLogger(__name__)


class MutationAnnotation(StateAnnotation):
    """Mutation Annotation

    This is the annotation used by the MutationPruner plugin to record mutations
    """

    def __init__(self):
        pass

    @property
    def persist_over_calls(self) -> bool:
        return True


class DependencyAnnotation(MergeableStateAnnotation):
    """Dependency Annotation

    This annotation tracks read and write access to the state during each transaction.
    """

    def __init__(self):
        self.storage_loaded = set()  # type: Set
        self.storage_written = {}  # type: Dict[int, Set]
        self.has_call = False  # type: bool
        self.path = [0]  # type: List
        self.blocks_seen = set()  # type: Set[int]

    def __copy__(self):
        result = DependencyAnnotation()
        result.storage_loaded = copy(self.storage_loaded)
        result.storage_written = copy(self.storage_written)
        result.has_call = self.has_call
        result.path = copy(self.path)
        result.blocks_seen = copy(self.blocks_seen)
        return result

    def get_storage_write_cache(self, iteration: int):
        return self.storage_written.get(iteration, set())

    def extend_storage_write_cache(self, iteration: int, value: object):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = set()
        self.storage_written[iteration].add(value)

    def check_merge_annotation(self, other: "DependencyAnnotation"):
        if not isinstance(other, DependencyAnnotation):
            raise TypeError("Expected an instance of DependencyAnnotation")
        return self.has_call == other.has_call and self.path == other.path

    def merge_annotation(self, other: "DependencyAnnotation"):
        merged_annotation = DependencyAnnotation()
        merged_annotation.blocks_seen = self.blocks_seen.union(other.blocks_seen)
        merged_annotation.has_call = self.has_call
        merged_annotation.path = copy(self.path)
        merged_annotation.storage_loaded = self.storage_loaded.union(
            other.storage_loaded
        )
        keys = set(
            list(other.storage_written.keys()) + list(self.storage_written.keys())
        )
        for key in keys:
            other_set = other.storage_written.get(key, set())
            merged_annotation.storage_written[key] = self.storage_written.get(
                key, set()
            ).union(other_set)
        return merged_annotation


class WSDependencyAnnotation(MergeableStateAnnotation):
    """Dependency Annotation for World state

    This  world state annotation maintains a stack of state annotations.
    It is used to transfer individual state annotations from one transaction to the next.
    """

    def __init__(self):
        self.annotations_stack: List[DependencyAnnotation] = []

    def __copy__(self):
        result = WSDependencyAnnotation()
        result.annotations_stack = copy(self.annotations_stack)
        return result

    def check_merge_annotation(self, annotation: "WSDependencyAnnotation") -> bool:
        if len(self.annotations_stack) != len(annotation.annotations_stack):
            # We can only merge worldstate annotations that have seen an equal amount of transactions
            # since the beginning of symbolic execution
            return False
        for a1, a2 in zip(self.annotations_stack, annotation.annotations_stack):
            if a1 == a2:
                continue
            if (
                isinstance(a1, MergeableStateAnnotation)
                and isinstance(a2, MergeableStateAnnotation)
                and a1.check_merge_annotation(a2) is True
            ):
                continue
            log.debug("Aborting merge between annotations {} and {}".format(a1, a2))
            return False

        return True

    def merge_annotation(
        self, annotation: "WSDependencyAnnotation"
    ) -> "WSDependencyAnnotation":
        merged_annotation = WSDependencyAnnotation()
        for a1, a2 in zip(self.annotations_stack, annotation.annotations_stack):
            if a1 == a2:
                merged_annotation.annotations_stack.append(copy(a1))
            merged_annotation.annotations_stack.append(a1.merge_annotation(a2))
        return merged_annotation
