"""This module contains the detection code to find multiple sends occurring in
a single transaction."""
from copy import copy
from typing import cast, List

from mythril.analysis.report import Issue
from mythril.analysis.solver import get_transaction_sequence, UnsatError
from mythril.analysis.swc_data import MULTIPLE_SENDS
from mythril.analysis.module.base import DetectionModule, EntryPoint
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


class MultipleSends(DetectionModule):
    """This module checks for multiple sends in a single transaction."""

    name = "Multiple external calls in the same transaction"
    swc_id = MULTIPLE_SENDS
    description = "Check for multiple sends in a single transaction"
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE", "RETURN", "STOP"]

    def _execute(self, state: GlobalState) -> None:
        if state.get_current_instruction()["address"] in self.cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add(issue.address)
        self.issues.extend(issues)

    @staticmethod
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
                        state, state.world_state.constraints
                    )
                except UnsatError:
                    continue
                description_tail = (
                    "This call is executed following another call within the same transaction. It is possible "
                    "that the call never gets executed if a prior call fails permanently. This might be caused "
                    "intentionally by a malicious callee. If possible, refactor the code such that each transaction "
                    "only executes one external call or "
                    "make sure that all callees can be trusted (i.e. they’re part of your own codebase)."
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


detector = MultipleSends()
