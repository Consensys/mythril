"""This module contains the detection code to find multiple sends occurring in
a single transaction."""
from copy import copy
from typing import cast, List, Optional

from mythril.analysis.ops import Call
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import MULTIPLE_SENDS
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
import logging
from mythril.analysis.call_helpers import get_call_from_state

log = logging.getLogger(__name__)


class MultipleSendsAnnotation(StateAnnotation):
    def __init__(self) -> None:
        self.calls = []  # type: List[Optional[Call]]

    def __copy__(self):
        result = MultipleSendsAnnotation()
        result.calls = copy(self.calls)
        return result


class MultipleSendsModule(DetectionModule):
    """This module checks for multiple sends in a single transaction."""

    def __init__(self):
        """"""
        super().__init__(
            name="Multiple Sends",
            swc_id=MULTIPLE_SENDS,
            description="Check for multiple sends in a single transaction",
            entrypoint="callback",
            pre_hooks=[
                "CALL",
                "DELEGATECALL",
                "STATICCALL",
                "CALLCODE",
                "RETURN",
                "STOP",
            ],
        )

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues


def _analyze_state(state: GlobalState):
    """
    :param state: the current state
    :return: returns the issues for that corresponding state
    """
    instruction = state.get_current_instruction()

    annotations = cast(
        List[MultipleSendsAnnotation],
        list(state.get_annotations(MultipleSendsAnnotation)),
    )
    if len(annotations) == 0:
        log.debug("Creating annotation for state")
        state.annotate(MultipleSendsAnnotation())
        annotations = cast(
            List[MultipleSendsAnnotation],
            list(state.get_annotations(MultipleSendsAnnotation)),
        )

    calls = annotations[0].calls

    if instruction["opcode"] in ["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"]:
        call = get_call_from_state(state)
        if call:
            calls += [call]

    else:  # RETURN or STOP
        if len(calls) > 1:

            description_tail = (
                "Consecutive calls are executed at the following bytecode offsets:\n"
            )

            for call in calls:
                description_tail += "Offset: {}\n".format(
                    call.state.get_current_instruction()["address"]
                )

            description_tail += (
                "Try to isolate each external call into its own transaction,"
                " as external calls can fail accidentally or deliberately.\n"
            )

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=instruction["address"],
                swc_id=MULTIPLE_SENDS,
                bytecode=state.environment.code.bytecode,
                title="Multiple Calls in a Single Transaction",
                severity="Medium",
                description_head="Multiple sends are executed in one transaction.",
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            return [issue]

    return []


detector = MultipleSendsModule()
