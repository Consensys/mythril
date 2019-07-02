"""This module contains the detection code to find multiple sends occurring in
a single transaction."""
from copy import copy
from typing import cast, List

from mythril.analysis.report import Issue
from mythril.analysis.solver import get_transaction_sequence, UnsatError
from mythril.analysis.swc_data import MULTIPLE_SENDS
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
import logging

log = logging.getLogger(__name__)


class MultipleSendsAnnotation(StateAnnotation):
    def __init__(self) -> None:
        self.call_offsets = []  # type: List[int]

    def __copy__(self):
        result = MultipleSendsAnnotation()
        result.call_offsets = copy(self.call_offsets)
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

    def _execute(self, state: GlobalState) -> None:
        self._issues.extend(_analyze_state(state))


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
        state.annotate(MultipleSendsAnnotation())
        annotations = cast(
            List[MultipleSendsAnnotation],
            list(state.get_annotations(MultipleSendsAnnotation)),
        )

    call_offsets = annotations[0].call_offsets

    if instruction["opcode"] in ["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"]:
        call_offsets.append(state.get_current_instruction()["address"])

    else:  # RETURN or STOP

        for offset in call_offsets[1:]:
            try:
                transaction_sequence = get_transaction_sequence(
                    state, state.mstate.constraints
                )
            except UnsatError:
                continue
            description_tail = (
                "This call is executed after a previous call in the same transaction. "
                "Try to isolate each call, transfer or send into its own transaction."
            )

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=offset,
                swc_id=MULTIPLE_SENDS,
                bytecode=state.environment.code.bytecode,
                title="Multiple Calls in a Single Transaction",
                severity="Low",
                description_head="Multiple calls are executed in the same transaction.",
                description_tail=description_tail,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                transaction_sequence=transaction_sequence,
            )

            return [issue]

    return []


detector = MultipleSendsModule()
