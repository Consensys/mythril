from mythril.analysis.ops import Call, Variable, VarType
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.call_helpers import get_call_from_state
from mythril.laser.smt import symbol_factory, simplify, UGT
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.analysis import solver
from mythril.exceptions import UnsatError
from typing import List, cast
from copy import copy

import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

Check whether there is a state change of the contract after the execution of an external call
"""


class CallIssue:
    """ This class is a struct of
        call: the Call struct
        user_defined_address: Whether the address can be defined by user or not
    """

    def __init__(self, call: Call, user_defined_address: bool) -> None:
        self.call = call
        self.user_defined_address = user_defined_address


class StateChangeCallsAnnotation(StateAnnotation):
    def __init__(self) -> None:
        self.calls = []  # type: List[CallIssue]

    def __copy__(self):
        result = StateChangeCallsAnnotation()
        result.calls = copy(self.calls)
        return result


class StateChange(DetectionModule):
    """This module searches for state change after low level calls (e.g. call.value()) that
    forward gas to the callee."""

    def __init__(self):
        """"""
        super().__init__(
            name="State Change After External calls",
            swc_id=REENTRANCY,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=[
                "CALL",
                "SSTORE",
                "DELEGATECALL",
                "STATICCALL",
                "CREATE",
                "CALLCODE",
            ],
        )

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(self._analyze_state(state))
        return self.issues

    @staticmethod
    def _add_external_call(
        state: GlobalState, annotations: List[StateChangeCallsAnnotation]
    ) -> None:
        call = get_call_from_state(state)
        gas = state.mstate.stack[-1]
        to = state.mstate.stack[-2]
        if call is None:
            return
        try:
            constraints = copy(state.node.constraints)
            solver.get_model(
                constraints + [UGT(gas, symbol_factory.BitVecVal(2300, 256))]
            )

            # Check whether we can also set the callee address
            try:
                constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
                solver.get_model(constraints)
                annotations[0].calls.append(
                    CallIssue(call=call, user_defined_address=True)
                )
            except UnsatError:
                annotations[0].calls.append(
                    CallIssue(call=call, user_defined_address=False)
                )

        except UnsatError:
            pass

    @staticmethod
    def _analyze_state(state) -> List[Issue]:
        """

        :param state:
        :return:
        """
        address = state.get_current_instruction()["address"]
        annotations = cast(
            List[StateChangeCallsAnnotation],
            list(state.get_annotations(StateChangeCallsAnnotation)),
        )
        if len(annotations) == 0:
            log.debug("Creating annotation for state")
            state.annotate(StateChangeCallsAnnotation())
            annotations = cast(
                List[StateChangeCallsAnnotation],
                list(state.get_annotations(StateChangeCallsAnnotation)),
            )
        opcode = state.get_current_instruction()["opcode"]

        if opcode in ("SSTORE", "CREATE", "CREATE2"):
            return StateChange._handle_state_change(
                state, address=address, annotation=annotations[0]
            )
        call = get_call_from_state(state)

        if call is None:
            return []

        if StateChange._balance_change(call.value):
            return StateChange._handle_state_change(
                state, address=address, annotation=annotations[0]
            )

        if opcode == "CALL":
            StateChange._add_external_call(state, annotations=annotations)

        return []

    @staticmethod
    def _get_state_change_issues(
        callissues: List[CallIssue], state: GlobalState, address: int
    ) -> List[Issue]:
        issues = []
        for callissue in callissues:
            severity = "Medium" if callissue.user_defined_address else "Low"
            call = callissue.call
            logging.debug(
                "[EXTERNAL_CALLS] Detected state changes at addresses: {}".format(
                    address
                )
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

    @staticmethod
    def _handle_state_change(
        state: GlobalState, address: int, annotation: StateChangeCallsAnnotation
    ) -> List[Issue]:
        calls = annotation.calls
        issues = StateChange._get_state_change_issues(calls, state, address)
        return issues

    @staticmethod
    def _balance_change(value: Variable) -> bool:
        if value.type == VarType.CONCRETE:
            return value.val > 0
        else:
            zero = symbol_factory.BitVecVal(0, 256)
            return simplify(value.val > zero)


detector = StateChange()
