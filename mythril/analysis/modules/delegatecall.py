"""This module contains the detection code for insecure delegate call usage."""
import logging
from typing import List

from mythril.analysis.potential_issues import (
    get_potential_issues_annotation,
    PotentialIssue,
)
from mythril.analysis.swc_data import DELEGATECALL_TO_UNTRUSTED_CONTRACT
from mythril.laser.ethereum.transaction.symbolic import ATTACKER_ADDRESS
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import symbol_factory, UGT

log = logging.getLogger(__name__)


class DelegateCallModule(DetectionModule):
    """This module detects calldata being forwarded using DELEGATECALL."""

    def __init__(self) -> None:
        """"""
        super().__init__(
            name="DELEGATECALL Usage in Fallback Function",
            swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
            description="Check for invocations of delegatecall(msg.data) in the fallback function.",
            entrypoint="callback",
            pre_hooks=["DELEGATECALL"],
        )

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
        if state.get_current_instruction()["address"] in self.cache:
            return
        potential_issues = self._analyze_state(state)

        annotation = get_potential_issues_annotation(state)
        annotation.potential_issues.extend(potential_issues)

    def _analyze_state(self, state: GlobalState) -> List[PotentialIssue]:
        """
        :param state: the current state
        :return: returns the issues for that corresponding state
        """
        gas = state.mstate.stack[-1]
        to = state.mstate.stack[-2]

        constraints = [
            to == ATTACKER_ADDRESS,
            UGT(gas, symbol_factory.BitVecVal(2300, 256)),
        ]

        for tx in state.world_state.transaction_sequence:
            if not isinstance(tx, ContractCreationTransaction):
                constraints.append(tx.caller == ATTACKER_ADDRESS)

        try:
            address = state.get_current_instruction()["address"]

            logging.debug(
                "[DELEGATECALL] Detected potential delegatecall to a user-supplied address : {}".format(
                    address
                )
            )

            description_head = "The contract delegates execution to another contract with a user-supplied address."
            description_tail = (
                "The smart contract delegates execution to a user-supplied address. Note that callers "
                "can execute arbitrary contracts and that the callee contract "
                "can access the storage of the calling contract. "
            )

            return [
                PotentialIssue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
                    bytecode=state.environment.code.bytecode,
                    title="Delegatecall Proxy To User-Supplied Address",
                    severity="Medium",
                    description_head=description_head,
                    description_tail=description_tail,
                    constraints=constraints,
                    detector=self,
                )
            ]

        except UnsatError:
            return []


detector = DelegateCallModule()
