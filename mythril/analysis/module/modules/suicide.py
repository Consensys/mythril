from mythril.analysis import solver
from mythril.analysis.report import Issue
from mythril.analysis.swc_data import UNPROTECTED_SELFDESTRUCT
from mythril.exceptions import UnsatError
from mythril.analysis.issue_annotation import IssueAnnotation
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.laser.smt.bool import And
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
import logging
from mythril.laser.ethereum.function_managers import keccak_function_manager


log = logging.getLogger(__name__)

DESCRIPTION = """
Check if the contact can be 'accidentally' killed by anyone.
For kill-able contracts, also check whether it is possible to direct the contract balance to the attacker.
"""


class AccidentallyKillable(DetectionModule):
    """This module checks if the contact can be 'accidentally' killed by
    anyone."""

    name = "Contract can be accidentally killed by anyone"
    swc_id = UNPROTECTED_SELFDESTRUCT
    description = DESCRIPTION
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["SELFDESTRUCT"]

    def __init__(self):
        super().__init__()
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
        return self._analyze_state(state)

    def _analyze_state(self, state):
        log.info("Suicide module: Analyzing suicide instruction")
        instruction = state.get_current_instruction()

        to = state.mstate.stack[-1]

        log.debug("SELFDESTRUCT in function %s", state.environment.active_function_name)

        description_head = "Any sender can cause the contract to self-destruct."

        attacker_constraints = []

        for tx in state.world_state.transaction_sequence:
            if not isinstance(tx, ContractCreationTransaction):
                attacker_constraints.append(
                    And(tx.caller == ACTORS.attacker, tx.caller == tx.origin)
                )
        try:
            try:
                constraints = (
                    state.world_state.constraints
                    + [to == ACTORS.attacker]
                    + attacker_constraints
                )
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )

                description_tail = (
                    "Any sender can trigger execution of the SELFDESTRUCT instruction to destroy this "
                    "contract account and withdraw its balance to an arbitrary address. Review the transaction trace "
                    "generated for this issue and make sure that appropriate security controls are in place to prevent "
                    "unrestricted access."
                )

            except UnsatError:
                constraints = state.world_state.constraints + attacker_constraints
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )
                description_tail = (
                    "Any sender can trigger execution of the SELFDESTRUCT instruction to destroy this "
                    "contract account. Review the transaction trace generated for this issue and make sure that "
                    "appropriate security controls are in place to prevent unrestricted access."
                )

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
            state.annotate(
                IssueAnnotation(
                    conditions=[And(*constraints)], issue=issue, detector=self
                )
            )

            return [issue]
        except UnsatError:
            log.debug("No model found")

        return []


detector = AccidentallyKillable()
