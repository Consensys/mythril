"""This module contains the detection code for unexpected ether balance."""
from mythril.analysis.report import Issue
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.swc_data import UNEXPECTED_ETHER_BALANCE
from mythril.analysis.module.base import DetectionModule
from mythril.analysis.module.module_helpers import is_prehook
from mythril.laser.smt import BitVec, And
from mythril.analysis.solver import UnsatError, get_transaction_sequence
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.laser.ethereum.state.global_state import GlobalState

import logging

log = logging.getLogger(__name__)

DESCRIPTION = """
Check for strict equality checks with contract balance
"""


class EtherBalanceCheckAnnotation(StateAnnotation):
    """State Annotation used if an overflow is both possible and used in the annotated path"""

    def __init__(self, balance: BitVec) -> None:
        self.balance = balance


class BalanceConditionAnnotation:
    """"""

    def __init__(self, address=None) -> None:
        self.address = address


class UnexpectedEther(DetectionModule):
    """This module checks for strict equality checks with contract balance."""

    author = "MythX Team"
    plugin_license = "All rights reserved - ConsenSys"
    plugin_type = "Detection Module"
    plugin_description = DESCRIPTION
    plugin_default_enabled = True

    name = "Unexpected Ether Balance"
    swc_id = "132"
    description = DESCRIPTION
    pre_hooks = ["INVALID", "EQ", "RETURN", "STOP"]
    post_hooks = ["BALANCE"]

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """

        return self._analyze_state(state)

    def _analyze_state(self, state):
        """

        :param state:
        :return:
        """
        node = state.node
        instruction = state.get_current_instruction()
        if is_prehook() is False:
            balance = state.mstate.stack[-1]
            annotations = state.get_annotations(EtherBalanceCheckAnnotation)
            for annotation in annotations:
                if annotation.balance == balance:
                    return []

            state.annotate(EtherBalanceCheckAnnotation(balance))
            return []

        if instruction["opcode"] == "EQ":
            op1, op2 = state.mstate.stack[-2:]
            annotations = list(state.get_annotations(EtherBalanceCheckAnnotation))
            op = None
            for annotation in annotations:
                if hash(annotation.balance) != hash(op1) and hash(
                    annotation.balance
                ) != hash(op2):
                    continue
                if hash(annotation.balance) == hash(op1):
                    op = op1
                else:
                    op = op2
                break
            if op is None:
                return []
            op.annotate(
                BalanceConditionAnnotation(
                    address=state.get_current_instruction()["address"]
                )
            )
            log.debug(
                "Equality check for contract balance in function " + node.function_name
            )
            return []

        for constraint in state.world_state.constraints:
            for annotation in constraint.get_annotations(BalanceConditionAnnotation):
                if annotation.address in self.cache:
                    continue
                try:
                    transaction_sequence = get_transaction_sequence(
                        state, state.world_state.constraints
                    )
                except UnsatError:
                    continue
                log.debug("Detected a strict equality check")
                title = "Strict Ether balance check"
                description_head = "Use of strict ether balance checking"
                description_tail = "Ether can be forcefully sent to this contract, This may make the contract unusable."

                issue = Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=annotation.address,
                    title=title,
                    bytecode=state.environment.code.bytecode,
                    swc_id=UNEXPECTED_ETHER_BALANCE,
                    severity="Low",
                    description_head=description_head,
                    description_tail=description_tail,
                    transaction_sequence=transaction_sequence,
                )
                state.annotate(
                    IssueAnnotation(
                        conditions=[And(*state.world_state.constraints)],
                        issue=issue,
                        detector=self,
                    )
                )

                return [issue]
        return []


detector = UnexpectedEther()
