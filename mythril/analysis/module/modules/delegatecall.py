"""This module contains the detection code for insecure delegate call usage."""
import logging
from typing import List

from mythril.analysis.potential_issues import (
    get_potential_issues_annotation,
    PotentialIssue,
)
from mythril.analysis.swc_data import DELEGATECALL_TO_UNTRUSTED_CONTRACT
from mythril.laser.ethereum.transaction.symbolic import ACTORS
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis.module.base import DetectionModule, EntryPoint
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import symbol_factory, UGT

log = logging.getLogger(__name__)


class ArbitraryDelegateCall(DetectionModule):
    """This module detects delegatecall to a user-supplied address."""

    name = "Delegatecall to a user-specified address"
    swc_id = DELEGATECALL_TO_UNTRUSTED_CONTRACT
    description = "Check for invocations of delegatecall to a user-supplied address."
    entry_point = EntryPoint.CALLBACK
    pre_hooks = ["DELEGATECALL"]

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
            to == ACTORS.attacker,
            UGT(gas, symbol_factory.BitVecVal(2300, 256)),
            state.new_bitvec(
                "retval_{}".format(state.get_current_instruction()["address"]), 256
            )
            == 1,
        ]

        for tx in state.world_state.transaction_sequence:
            if not isinstance(tx, ContractCreationTransaction):
                constraints.append(tx.caller == ACTORS.attacker)

        try:
            address = state.get_current_instruction()["address"]

            logging.debug(
                "[DELEGATECALL] Detected potential delegatecall to a user-supplied address : {}".format(
                    address
                )
            )

            description_head = "The contract delegates execution to another contract with a user-supplied address."
            description_tail = (
                "The smart contract delegates execution to a user-supplied address.This could allow an attacker to "
                "execute arbitrary code in the context of this contract account and manipulate the state of the "
                "contract account or execute actions on its behalf."
            )

            return [
                PotentialIssue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
                    bytecode=state.environment.code.bytecode,
                    title="Delegatecall to user-supplied address",
                    severity="High",
                    description_head=description_head,
                    description_tail=description_tail,
                    constraints=constraints,
                    detector=self,
                )
            ]

        except UnsatError:
            return []


detector = ArbitraryDelegateCall()
