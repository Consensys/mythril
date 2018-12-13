from mythril.analysis.report import Issue
from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.smt import UGT, symbol_factory
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for low level calls (e.g. call.value()) that forward all gas to the callee.
Report a warning if the callee address can be set by the sender, otherwise create 
an informational issue.

"""


def _analyze_state(state):

    node = state.node
    gas = state.mstate.stack[-1]
    to = state.mstate.stack[-2]

    address = state.get_current_instruction()["address"]

    try:
        constraints = node.constraints
        transaction_sequence = solver.get_transaction_sequence(
            state, constraints + [UGT(gas, symbol_factory.BitVecVal(2300, 256))]
        )

        # Check whether we can also set the callee address

        try:
            constraints += [to == 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF]
            transaction_sequence = solver.get_transaction_sequence(state, constraints)

            debug = str(transaction_sequence)
            description = (
                "The contract executes a function call with high gas to a user-supplied address. "
                "Note that the callee can contain arbitrary code and may re-enter any function in this contract. "
                "Review the business logic carefully to prevent unanticipated effects on the contract state."
            )

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External call to user-supplied address",
                _type="Warning",
                bytecode=state.environment.code.bytecode,
                description=description,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

        except UnsatError:

            log.debug(
                "[EXTERNAL_CALLS] Callee address cannot be modified. Reporting informational issue."
            )

            debug = str(transaction_sequence)
            description = (
                "The contract executes a function call to an external address. "
                "Verify that the code at this address is trusted and immutable."
            )

            issue = Issue(
                contract=node.contract_name,
                function_name=state.node.function_name,
                address=address,
                swc_id=REENTRANCY,
                title="External call",
                _type="Informational",
                bytecode=state.environment.code.bytecode,
                description=description,
                debug=debug,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

    except UnsatError:
        log.debug("[EXTERNAL_CALLS] No model found.")
        return []

    return [issue]


class ExternalCalls(DetectionModule):
    """This module searches for low level calls (e.g. call.value()) that forward all gas to the callee."""
    def __init__(self):
        super().__init__(
            name="External calls",
            swc_id=REENTRANCY,
            hooks=["CALL"],
            description=DESCRIPTION,
            entrypoint="callback",
        )
        self._issues = []

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues

    @property
    def issues(self):
        """

        :return:
        """
        return self._issues


detector = ExternalCalls()
