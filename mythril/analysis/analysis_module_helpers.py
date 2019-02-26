from mythril.analysis.ops import Call
from mythril.laser.ethereum.state.annotation import StateAnnotation

from typing import List
from copy import copy


class CallIssue:
    """ This class is a struct of
        call: the Call struct
        user_defined_address: Whether the address can be defined by user or not
    """

    def __init__(self, call: Call, user_defined_address: bool) -> None:
        self.call = call
        self.user_defined_address = user_defined_address


class ExternalCallsAnnotation(StateAnnotation):
    def __init__(self) -> None:
        self.calls = []  # type: List[CallIssue]

    def __copy__(self):
        result = ExternalCallsAnnotation()
        result.calls = copy(self.calls)
        return result
