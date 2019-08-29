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


class DelegateCallAnnotation(StateAnnotation):
    def __init__(self, call_state: GlobalState, constraints: List) -> None:
        """
        Initialize DelegateCall Annotation
        :param call_state: Call state
        """
        self.call_state = call_state
        self.constraints = constraints
        self.return_value = call_state.new_bitvec(
            "retval_{}".format(call_state.get_current_instruction()["address"]), 256
        )

    def _copy__(self):
        return DelegateCallAnnotation(self.call_state, copy(self.constraints))

    def get_issue(self, global_state: GlobalState, transaction_sequence: Dict) -> Issue:
        """
        Returns Issue for the annotation
        :param global_state: Global State
        :param transaction_sequence: Transaction sequence
        :return: Issue
        """

        address = self.call_state.get_current_instruction()["address"]
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

        return Issue(
            contract=self.call_state.environment.active_account.contract_name,
            function_name=self.call_state.environment.active_function_name,
            address=address,
            swc_id=DELEGATECALL_TO_UNTRUSTED_CONTRACT,
            title="Delegatecall Proxy To User-Supplied Address",
            bytecode=global_state.environment.code.bytecode,
            severity="Medium",
            description_head=description_head,
            description_tail=description_tail,
            transaction_sequence=transaction_sequence,
            gas_used=(
                global_state.mstate.min_gas_used,
                global_state.mstate.max_gas_used,
            ),
        )


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
        if state.get_current_instruction()["address"] in self._cache:
            return
        issues = self._analyze_state(state)
        for issue in issues:
            self._cache.add(issue.address)
        self._issues.extend(issues)

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
            return [
                DelegateCallAnnotation(state, constraints).get_issue(
                    state, transaction_sequence=transaction_sequence
                )
            ]
        except UnsatError:
            return []


detector = DelegateCallModule()
