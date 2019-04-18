"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.laser.smt import UGT, symbol_factory
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
            constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
            transaction_sequence = solver.get_transaction_sequence(state, constraints)

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

            log.debug(
                "[EXTERNAL_CALLS] Callee address cannot be modified. Reporting informational issue."
            )

            debug = json.dumps(transaction_sequence, indent=4)
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

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues


detector = ExternalCalls()
