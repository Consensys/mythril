from copy import copy

from mythril.analysis.report import Issue
from mythril.analysis.swc_data import MULTIPLE_SENDS
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
import logging
from mythril.analysis.call_helpers import get_call_from_state

log = logging.getLogger(__name__)


class MultipleSendsAnnotation(StateAnnotation):
    def __init__(self):
        self.calls = []

    def __copy__(self):
        result = MultipleSendsAnnotation()
        result.calls = copy(self.calls)
        return result


class MultipleSendsModule(DetectionModule):
    def __init__(self):
        super().__init__(
            name="Multiple Sends",
            swc_id=MULTIPLE_SENDS,
            pre_hooks=[
                "CALL",
                "DELEGATECALL",
                "STATICCALL",
                "CALLCODE",
                "RETURN",
                "STOP",
            ],
            post_hooks=[],
            description="Check for multiple sends in a single transaction",
            entrypoint="callback",
        )
        self._issues = []

    def execute(self, state: GlobalState):
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        return self._issues


def _analyze_state(state: GlobalState):
    """
    :param state: the current state
    :return: returns the issues for that corresponding state
    """
    node = state.node
    instruction = state.get_current_instruction()

    annotations = [a for a in state.get_annotations(MultipleSendsAnnotation)]
    if len(annotations) == 0:
        log.debug("Creating annotation for state")
        state.annotate(MultipleSendsAnnotation())
        annotations = [a for a in state.get_annotations(MultipleSendsAnnotation)]

    calls = annotations[0].calls

    if instruction["opcode"] in ["CALL", "DELEGATECALL", "STATICCALL", "CALLCODE"]:
        call = get_call_from_state(state)
        if call:
            calls += [call]

    else:  # RETURN or STOP
        if len(calls) > 1:
            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=instruction["address"],
                swc_id=MULTIPLE_SENDS,
                bytecode=state.environment.code.bytecode,
                title="Multiple Calls",
                _type="Informational",
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            issue.description = (
                "Multiple sends are executed in a single transaction. "
                "Try to isolate each external call into its own transaction,"
                " as external calls can fail accidentally or deliberately.\nConsecutive calls: \n"
            )

            for call in calls:
                issue.description += "Call at address: {}\n".format(
                    call.state.get_current_instruction()["address"]
                )

            return [issue]

    return []


detector = MultipleSendsModule()
