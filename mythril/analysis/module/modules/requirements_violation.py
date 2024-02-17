"""This module contains the detection code for requirement violations in a call"""
import logging

from mythril.analysis import solver
from mythril.analysis.module.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.laser.smt import And
from mythril.analysis.swc_data import REQUIREMENT_VIOLATION
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState

from typing import List

log = logging.getLogger(__name__)


class RequirementsViolation(DetectionModule):
    """This module detects transaction order dependence"""

    name = "Requirement Violation"
    swc_id = REQUIREMENT_VIOLATION
    description = "Checks whether any requirements violate in a call."
    entrypoint = "callback"
    pre_hooks = ["REVERT"]
    plugin_default_enabled = True

    def _execute(self, state: GlobalState) -> List[Issue]:
        """

        :param state:
        :return:
        """
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add((issue.source_location, issue.bytecode_hash))
        return issues

    def _analyze_state(self, state) -> List[Issue]:
        """

        :param state:
        :return:
        """

        if len(state.transaction_stack) < 2:
            return []

        try:
            address = state.get_current_instruction()["address"]
            description_head = "A requirement was violated in a nested call and the call was reverted as a result."
            description_tail = "Make sure valid inputs are provided to the nested call (for instance, via passed arguments)."
            transaction_sequence = solver.get_transaction_sequence(
                state, state.world_state.constraints
            )
            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=REQUIREMENT_VIOLATION,
                title="requirement violation",
                severity="Medium",
                description_head=description_head,
                description_tail=description_tail,
                bytecode=state.environment.code.bytecode,
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            state.annotate(
                IssueAnnotation(
                    conditions=[And(*state.world_state.constraints)],
                    issue=issue,
                    detector=self,
                )
            )

            return [issue]

        except UnsatError:
            log.debug("no model found")

        return []


detector = RequirementsViolation()
