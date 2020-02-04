"""This module contains the detection code for transaction order dependence
calls."""

from mythril.analysis import solver
from mythril.analysis.potential_issues import (
    PotentialIssue,
    get_potential_issues_annotation,
)
from mythril.analysis.swc_data import TX_ORDER_DEPENDENCE
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.smt import Or, Bool
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for low level calls (e.g. call.value()) that forward all gas to the callee.
Report a warning if the callee address can be set by the sender, otherwise create 
an informational issue.

"""


class BalanceAnnotation:
    def __init__(self, caller):
        self.caller = caller


class StorageAnnotation:
    def __init__(self, caller):
        self.caller = caller


class TransactionOrderDependence(DetectionModule):
    """This module searches for transaction order dependence."""

    def __init__(self):
        """"""
        super().__init__(
            name="Transaction Order Dependence",
            swc_id=TX_ORDER_DEPENDENCE,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["CALL"],
            post_hooks=["BALANCE", "SLOAD"],
        )

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        potential_issues = self._analyze_state(state)

        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(potential_issues)

    @staticmethod
    def annotate_balance_storage_vals(state, opcode):
        val = state.mstate.stack[-1]
        if opcode == "BALANCE":
            annotation = BalanceAnnotation
        else:
            annotation = StorageAnnotation
        if len(val.get_annotations(annotation)) == 0:
            state.mstate.stack[-1].annotate(annotation(state.environment.sender))
        return []

    def _analyze_state(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        opcode = state.get_current_instruction()["opcode"]
        if opcode != "CALL":
            opcode = state.environment.code.instruction_list[state.mstate.pc - 1][
                "opcode"
            ]
        if opcode in ("BALANCE", "SLOAD"):
            self.annotate_balance_storage_vals(state, opcode)
            return []

        value = state.mstate.stack[-3]
        if (
            len(value.get_annotations(StorageAnnotation))
            + len(value.get_annotations(BalanceAnnotation))
            == 0
        ):
            return []
        callers = []

        storage_annotations = value.get_annotations(StorageAnnotation)
        if len(storage_annotations) == 1:
            callers.append(storage_annotations[0].caller)
        balance_annotations = value.get_annotations(BalanceAnnotation)
        if len(balance_annotations) == 1:
            callers.append(balance_annotations[0].caller)

        address = state.get_current_instruction()["address"]
        call_constraint = Bool(False)
        for caller in callers:
            call_constraint = Or(call_constraint, ACTORS.attacker == caller)

        try:
            constraints = state.world_state.constraints + [call_constraint]

            solver.get_transaction_sequence(state, constraints)

            description_head = "Transaction Order dependence."
            description_tail = (
                "The callee address of an external message call can be set by "
                "the caller. Note that the callee can contain arbitrary code and may re-enter any function "
                "in this contract. Review the business logic carefully to prevent averse effects on the "
                "contract state."
            )

            issue = PotentialIssue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=TX_ORDER_DEPENDENCE,
                title="Transaction Order Dependence",
                bytecode=state.environment.code.bytecode,
                severity="Medium",
                description_head=description_head,
                description_tail=description_tail,
                constraints=constraints,
                detector=self,
            )

        except UnsatError:
            log.debug("[Transaction Order Dependence] No model found.")
            return []

        return [issue]


detector = TransactionOrderDependence()
