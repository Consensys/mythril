"""This module contains the detection code for unauthorized ether
withdrawal."""
import logging
import json
from copy import copy

from mythril.analysis import solver
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.laser.ethereum.transaction.symbolic import (
    ATTACKER_ADDRESS,
    CREATOR_ADDRESS,
)
from mythril.analysis.swc_data import UNPROTECTED_ETHER_WITHDRAWAL
from mythril.exceptions import UnsatError
from mythril.laser.ethereum.transaction import ContractCreationTransaction
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.smt import (
    UGT,
    Sum,
    symbol_factory,
    BVAddNoOverflow,
    If,
    simplify,
    UGE,
)

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for cases where Ether can be withdrawn to a user-specified address. 

An issue is reported if:

- The transaction sender does not match contract creator;
- The sender address can be chosen arbitrarily;
- The receiver address is identical to the sender address;
- The sender can withdraw *more* than the total amount they sent over all transactions.

"""


class EtherThief(DetectionModule):
    """This module search for cases where Ether can be withdrawn to a user-
    specified address."""

    def __init__(self):
        """"""
        super().__init__(
            name="Ether Thief",
            swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["CALL"],
        )

    def reset_module(self):
        """
        Resets the module by clearing everything
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
        """

        :param state:
        :return:
        """
        state = copy(state)
        instruction = state.get_current_instruction()

        value = state.mstate.stack[-3]
        target = state.mstate.stack[-2]

        constraints = copy(state.mstate.constraints)

        """
        Require that the current transaction is sent by the attacker and
        that the Ether sent to the attacker's address is greater than the
        amount of Ether the attacker sent.
        """
        attacker_address_bitvec = symbol_factory.BitVecVal(ATTACKER_ADDRESS, 256)

        constraints += [
            UGE(
                state.world_state.balances[state.environment.active_account.address],
                value,
            )
        ]
        state.world_state.balances[attacker_address_bitvec] += value
        state.world_state.balances[state.environment.active_account.address] -= value

        constraints += [
            UGT(
                state.world_state.balances[attacker_address_bitvec],
                state.world_state.starting_balances[attacker_address_bitvec],
            ),
            target == ATTACKER_ADDRESS,
            state.current_transaction.caller == ATTACKER_ADDRESS,
        ]

        try:
            transaction_sequence = solver.get_transaction_sequence(state, constraints)

            issue = Issue(
                contract=state.environment.active_account.contract_name,
                function_name=state.environment.active_function_name,
                address=instruction["address"],
                swc_id=UNPROTECTED_ETHER_WITHDRAWAL,
                title="Unprotected Ether Withdrawal",
                severity="High",
                bytecode=state.environment.code.bytecode,
                description_head="Anyone can withdraw ETH from the contract account.",
                description_tail="Arbitrary senders other than the contract creator can withdraw ETH from the contract"
                + " account without previously having sent an equivalent amount of ETH to it. This is likely to be"
                + " a vulnerability.",
                transaction_sequence=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )
        except UnsatError:
            log.debug("[ETHER_THIEF] no model found")
            return []

        return [issue]


detector = EtherThief()
