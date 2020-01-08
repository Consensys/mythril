"""This module contains the detection code for reachable exceptions."""
import logging
import json

from mythril.analysis import solver
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import REQUIREMENT_VIOLATION
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.analysis.analysis_module_helpers import is_prehook

log = logging.getLogger(__name__)

CALL_OPCODES = ["CALL", "DELEGATECALL", "CALLCODE", "STATICCALL"]


class ReachableExceptionsModule(DetectionModule):
    """"""

    def __init__(self):
        """"""
        super().__init__(
            name="Reachable Exceptions",
            swc_id=REQUIREMENT_VIOLATION,
            description="Checks whether any exception states are reachable.",
            entrypoint="callback",
            pre_hooks=["REVERT"],
        )

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if state.get_current_instruction()["address"] in self.cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add(issue.address)
        self.issues.extend(issues)

    @staticmethod
    def _analyze_state(state) -> list:
        """

        :param state:
        :return:
        """

        if len(state.transaction_stack) < 2:
            return []

        try:
            address = state.get_current_instruction()["address"]

            description_tail = "The requirement is too strong"
            transaction_sequence = solver.get_transaction_sequence(
                state, state.world_state.constraints
            )
            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=address,
                swc_id=REQUIREMENT_VIOLATION,
                title="Requirement violation",
                severity="Low",
                description_head="The requirement for this call can be violated.",
                description_tail=description_tail,
                bytecode=state.environment.code.bytecode,
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            return [issue]

        except UnsatError:
            log.debug("no model found")

        return []


detector = ReachableExceptionsModule()
