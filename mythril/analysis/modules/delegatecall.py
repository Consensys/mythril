"""This module contains the detection code for insecure delegate call usage."""
import json
import logging
from copy import copy
from typing import List, cast, Dict

from mythril.analysis import solver
from mythril.analysis.swc_data import DELEGATECALL_TO_UNTRUSTED_CONTRACT
from mythril.laser.ethereum.transaction.symbolic import ATTACKER_ADDRESS
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis.report import Issue
from mythril.analysis.modules.base import DetectionModule
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.state.annotation import StateAnnotation
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
        issues = self._analyze_state(state)
        for issue in issues:
            self.cache.add(issue.address)
        self.issues.extend(issues)

    @staticmethod
    def _analyze_state(state: GlobalState) -> List[Issue]:
        """
        :param state: the current state
        :return: returns the issues for that corresponding state
        """
        op_code = state.get_current_instruction()["opcode"]

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
            transaction_sequence = solver.get_transaction_sequence(
                state, state.mstate.constraints + constraints
            )

            address = state.get_current_instruction()["address"]
            logging.debug(
                "[DELEGATECALL] Detected delegatecall to a user-supplied address : {}".format(
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
                Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
                    bytecode=state.environment.code.bytecode,
                    title="Delegatecall Proxy To User-Supplied Address",
                    severity="Medium",
                    description_head=description_head,
                    description_tail=description_tail,
                    transaction_sequence=transaction_sequence,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )
            ]

        except UnsatError:
            return []


detector = DelegateCallModule()
