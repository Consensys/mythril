from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.symbolic import ATTACKER_ADDRESS
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """
Check if the contact can be 'accidentally' killed by anyone.
For kill-able contracts, also check whether it is possible to direct the contract balance to the attacker.
"""


class SuicideModule(DetectionModule):
    """This module checks if the contact can be 'accidentally' killed by
    anyone."""

    def __init__(self):
        super().__init__(
            name="Unprotected Selfdestruct",
            swc_id=UNPROTECTED_SELFDESTRUCT,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["SUICIDE"],
        )
        self._cache_address = {}

    def reset_module(self):
        """
        Resets the module
        :return:
        """
        super().reset_module()

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if state.get_current_instruction()["address"] in self._cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self._cache.add(issue.address)
        self._issues.extend(issues)

    @staticmethod
    def _analyze_state(state):
        log.info("Suicide module: Analyzing suicide instruction")
        instruction = state.get_current_instruction()

        to = state.mstate.stack[-1]

        log.debug(
            "[SUICIDE] SUICIDE in function " + state.environment.active_function_name
        )

        description_head = "The contract can be killed by anyone."

        constraints = []

        for tx in state.world_state.transaction_sequence:
            if not isinstance(tx, ContractCreationTransaction):
                constraints.append(tx.caller == ATTACKER_ADDRESS)

        try:
            try:
                transaction_sequence = solver.get_transaction_sequence(
                    state,
                    state.mstate.constraints + constraints + [to == ATTACKER_ADDRESS],
                )
                description_tail = (
                    "Anyone can kill this contract and withdraw its balance to an arbitrary "
                    "address."
                )
            except UnsatError:
                transaction_sequence = solver.get_transaction_sequence(
                    state, state.mstate.constraints + constraints
                )
                description_tail = "Arbitrary senders can kill this contract."

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=instruction["address"],
                swc_id=UNPROTECTED_SELFDESTRUCT,
                bytecode=state.environment.code.bytecode,
                title="Unprotected Selfdestruct",
                severity="High",
                description_head=description_head,
                description_tail=description_tail,
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
            return [issue]
        except UnsatError:
            try:
                solver.get_model(tuple(state.mstate.constraints[:-1]))
            except UnsatError:
                print("Failed")
            log.info("[UNCHECKED_SUICIDE] no model found")

        return []


detector = SuicideModule()
