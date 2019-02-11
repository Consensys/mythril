"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.ops import Call, Variable, VarType
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.call_helpers import get_call_from_state
from mythril.laser.smt import UGT, symbol_factory, simplify
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
from copy import copy
from typing import List, cast
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for low level calls (e.g. call.value()) that forward all gas to the callee.
Report a warning if the callee address can be set by the sender, otherwise create 
an informational issue.

"""


class CallIssue:
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


def _get_state_change_issues(
    callissues: List[CallIssue], state: GlobalState, address: int
) -> List[Issue]:
    issues = []
    for callissue in callissues:
        severity = "Medium" if callissue.user_defined_address else "Low"
        call = callissue.call
        logging.debug(
            "[EXTERNAL_CALLS] Detected state changes at addresses: {}".format(address)
        )
        description_head = (
            "The contract account state is changed after an external call. "
        )
        description_tail = (
            "Consider that the called contract could re-enter the function before this "
            "state change takes place. This can lead to business logic vulnerabilities."
        )

        issue = Issue(
            contract=call.node.contract_name,
            function_name=call.node.function_name,
            address=address,
            title="State change after external call",
            severity=severity,
            description_head=description_head,
            description_tail=description_tail,
            swc_id=REENTRANCY,
            bytecode=state.environment.code.bytecode,
        )
        issues.append(issue)
    return issues


def _handle_state_change(
    state: GlobalState, address: int, annotation: ExternalCallsAnnotation
) -> List[Issue]:
    calls = annotation.calls
    issues = _get_state_change_issues(calls, state, address)
    return issues


def _balance_change(value: Variable) -> bool:
    if value.type == VarType.CONCRETE:
        return value.val > 0
    else:
        zero = symbol_factory.BitVecVal(0, 256)
        return simplify(value.val > zero)


def _analyze_state(state):
    """

    :param state:
    :return:
    """
    node = state.node
    gas = state.mstate.stack[-1]
    to = state.mstate.stack[-2]
    issues = []
    address = state.get_current_instruction()["address"]
    annotations = cast(
        List[ExternalCallsAnnotation],
        list(state.get_annotations(ExternalCallsAnnotation)),
    )
    if len(annotations) == 0:
        log.debug("Creating annotation for state")
        state.annotate(ExternalCallsAnnotation())
        annotations = cast(
            List[ExternalCallsAnnotation],
            list(state.get_annotations(ExternalCallsAnnotation)),
        )

    if state.get_current_instruction()["opcode"] == "SSTORE":
        return _handle_state_change(state, address=address, annotation=annotations[0])
    call = get_call_from_state(state)

    if call is None:
        return []

    if _balance_change(call.value):
        return _handle_state_change(state, address=address, annotation=annotations[0])

    try:
        constraints = node.constraints
        transaction_sequence = solver.get_transaction_sequence(
            state, constraints + [UGT(gas, symbol_factory.BitVecVal(2300, 256))]
        )

        # Check whether we can also set the callee address

        try:
            constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
            transaction_sequence = solver.get_transaction_sequence(state, constraints)

            debug = json.dumps(transaction_sequence, indent=4)
            description_head = "A call to a user-supplied address is executed."
            description_tail = (
                "The callee address of an external message call can be set by "
                "the caller. Note that the callee can contain arbitrary code and may re-enter any function "
                "in this contract. Review the business logic carefully to prevent averse effects on the"
                "contract state."
            )

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External Call To User-Supplied Address",
                bytecode=state.environment.code.bytecode,
                severity="Medium",
                description_head=description_head,
                description_tail=description_tail,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            annotations[0].calls.append(CallIssue(call=call, user_defined_address=True))

        except UnsatError:

            log.debug(
                "[EXTERNAL_CALLS] Callee address cannot be modified. Reporting informational issue."
            )

            debug = json.dumps(transaction_sequence, indent=4)
            description_head = "The contract executes an external message call."
            description_tail = (
                "An external function call to a fixed contract address is executed. Make sure "
                "that the callee contract has been reviewed carefully."
            )

            issue = Issue(
                contract=node.contract_name,
                function_name=state.node.function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External Call To Fixed Address",
                bytecode=state.environment.code.bytecode,
                severity="Low",
                description_head=description_head,
                description_tail=description_tail,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            annotations[0].calls.append(
                CallIssue(call=call, user_defined_address=False)
            )

    except UnsatError:
        log.debug("[EXTERNAL_CALLS] No model found.")
        return []
    issues.append(issue)
    return issues


class ExternalCalls(DetectionModule):
    """This module searches for low level calls (e.g. call.value()) that
    forward all gas to the callee."""

    def __init__(self):
        """"""
        super().__init__(
            name="External calls",
            swc_id=REENTRANCY,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["CALL", "SSTORE"],
        )

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues


detector = ExternalCalls()
