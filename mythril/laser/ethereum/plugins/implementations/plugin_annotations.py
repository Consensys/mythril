from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.smt import If

from copy import copy
from typing import Dict, List, Set


class MutationAnnotation(StateAnnotation):
    """Mutation Annotation

    This is the annotation used by the MutationPruner plugin to record mutations
    """

    def __init__(self):
        pass


class DependencyAnnotation(StateAnnotation):
    """Dependency Annotation

    This annotation tracks read and write access to the state during each transaction.
    """

    def __init__(self):
        self.storage_loaded = []  # type: List
        self.storage_written = {}  # type: Dict[int, List]
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
        if iteration not in self.storage_written:
            self.storage_written[iteration] = []

        return self.storage_written[iteration]

    def extend_storage_write_cache(self, iteration: int, value: object):
        if iteration not in self.storage_written:
            self.storage_written[iteration] = [value]
        elif value not in self.storage_written[iteration]:
            self.storage_written[iteration].append(value)

    def check_merge_annotation(self, other):
        return self.has_call == other.has_call and self.path == other.path

    def merge_annotation(self, other: "DependencyAnnotation"):
        self.blocks_seen = self.blocks_seen.union(other.blocks_seen)
        for v in other.storage_loaded:
            if v not in self.storage_loaded:
                self.storage_loaded.append(v)
        for key, val in other.storage_written.items():
            if key not in self.storage_written:
                self.storage_written[key] = val
            elif self.storage_written[key] != val:
                self.storage_written[key] += val


class WSDependencyAnnotation(StateAnnotation):
    """Dependency Annotation for World state

    This  world state annotation maintains a stack of state annotations.
    It is used to transfer individual state annotations from one transaction to the next.
    """

    def __init__(self):
        self.annotations_stack = []

    def __copy__(self):
        result = WSDependencyAnnotation()
        result.annotations_stack = copy(self.annotations_stack)
        return result

    def check_merge_annotation(self, other):
        if len(self.annotations_stack) != len(other.annotations_stack):
            return False
        for a1, a2 in zip(self.annotations_stack, other.annotations_stack):
            if a1.check_merge_annotation(a2) is False:
                return False
        return True

    def merge_annotations(self, other):
        for a1, a2 in zip(self.annotations_stack, other.annotations_stack):
            a1.merge_annotation(a2)
