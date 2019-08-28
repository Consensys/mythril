"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.laser.ethereum.transaction.symbolic import ATTACKER_ADDRESS
from mythril.laser.ethereum.transaction.transaction_models import (
    ContractCreationTransaction,
)
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.laser.smt import UGT, symbol_factory, Or, BitVec
from mythril.laser.ethereum.natives import PRECOMPILE_COUNT
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
from copy import copy
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for low level calls (e.g. call.value()) that forward all gas to the callee.
Report a warning if the callee address can be set by the sender, otherwise create 
an informational issue.

"""


def _is_precompile_call(global_state: GlobalState):
    to = global_state.mstate.stack[-2]  # type: BitVec
    constraints = copy(global_state.mstate.constraints)
    constraints += [
        Or(
            to < symbol_factory.BitVecVal(1, 256),
            to > symbol_factory.BitVecVal(PRECOMPILE_COUNT, 256),
        )
    ]

    try:
        solver.get_model(constraints)
        return False
    except UnsatError:
        return True


class ExternalCalls(DetectionModule):
    """This module searches for low level calls (e.g. call.value()) that
    forward all gas to the callee."""

    def __init__(self):
        """"""
        super().__init__(
            name="External calls",
            swc_id=REENTRANCY,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["CALL"],
        )

    def _execute(self, state: GlobalState) -> None:
        """

        :param state:
        :return:
        """
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
        gas = state.mstate.stack[-1]
        to = state.mstate.stack[-2]

        address = state.get_current_instruction()["address"]

        try:
            constraints = copy(state.mstate.constraints)

            transaction_sequence = solver.get_transaction_sequence(
                state, constraints + [UGT(gas, symbol_factory.BitVecVal(2300, 256))]
            )

            # Check whether we can also set the callee address

            try:
                constraints += [to == ATTACKER_ADDRESS]

                for tx in state.world_state.transaction_sequence:
                    if not isinstance(tx, ContractCreationTransaction):
                        constraints.append(tx.caller == ATTACKER_ADDRESS)

                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )

                description_head = "A call to a user-supplied address is executed."
                description_tail = (
                    "The callee address of an external message call can be set by "
                    "the caller. Note that the callee can contain arbitrary code and may re-enter any function "
                    "in this contract. Review the business logic carefully to prevent averse effects on the "
                    "contract state."
                )

                issue = Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=REENTRANCY,
                    title="External Call To User-Supplied Address",
                    bytecode=state.environment.code.bytecode,
                    severity="Medium",
                    description_head=description_head,
                    description_tail=description_tail,
                    transaction_sequence=transaction_sequence,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )

            except UnsatError:
                if _is_precompile_call(state):
                    return []

                log.debug(
                    "[EXTERNAL_CALLS] Callee address cannot be modified. Reporting informational issue."
                )

                description_head = "The contract executes an external message call."
                description_tail = (
                    "An external function call to a fixed contract address is executed. Make sure "
                    "that the callee contract has been reviewed carefully."
                )

                issue = Issue(
                    contract=state.environment.active_account.contract_name,
                    function_name=state.environment.active_function_name,
                    address=address,
                    swc_id=REENTRANCY,
                    title="External Call To Fixed Address",
                    bytecode=state.environment.code.bytecode,
                    severity="Low",
                    description_head=description_head,
                    description_tail=description_tail,
                    transaction_sequence=transaction_sequence,
                    gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
                )

        except UnsatError:
            log.debug("[EXTERNAL_CALLS] No model found.")
            return []

        return [issue]


detector = ExternalCalls()
