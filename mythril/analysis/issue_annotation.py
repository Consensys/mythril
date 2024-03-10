from typing import List

from mythril.analysis.report import Issue
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.smt import Bool
from copy import deepcopy


class IssueAnnotation(StateAnnotation):
    def __init__(self, conditions: List[Bool], issue: Issue, detector):
        """
        Issue Annotation to propagate issues
        - conditions: A list of independent conditions [a, b, c, ...]
                      Each of these have to be independently be satisfied
        - issue: The issue of the annotation
        - detector: The detection module
        """
        self.conditions = conditions
        self.issue = issue
        self.detector = detector

    def persist_to_world_state(self) -> bool:
        return True

    @property
    def persist_over_calls(self) -> bool:
        return True

    def __copy__(self):
        return IssueAnnotation(
            conditions=deepcopy(self.conditions),
            issue=self.issue,
            detector=self.detector,
        )

    def check_merge_annotation(self, annotation: "IssueAnnotation") -> bool:
        if self.conditions == annotation.conditions:
            return False
        if self.issue.address != annotation.issue.address:
            return False
        if type(self.detector) != type(annotation.detector):
            return False

        return True

    def merge_annotation(self, annotation: "IssueAnnotation") -> "IssueAnnotation":
        return self
