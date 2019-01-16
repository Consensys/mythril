"""This module checks for the Constantinople reentrancy vulnerability reported by ChainSecurity."""

from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.laser.ethereum.plugins.mutation_pruner import MutationAnnotation
from mythril.analysis.report import Issue
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.exceptions import UnsatError
import logging

log = logging.getLogger(__name__)

DESCRIPTION = """

This module reports an issue when:

1. The STOP or RETURN instruction is reached AND
2. A state variable has been modified during the transaction AND
2. The minimum gas used by the transaction is less than or equal to 1600.


"""


def _analyze_state(state):
    """
    :param state:
    :return:
    """
    node = state.node

    if len(list(state.get_annotations(MutationAnnotation))) > 0:

        if state.mstate.min_gas_used <= 1600:

            # Verify that this state is reachable

            try:
                constraints = node.constraints
                transaction_sequence = solver.get_transaction_sequence(
                    state, constraints
                )

            except UnsatError:
                log.debug("State is unreachable.")
                return []

            issue = Issue(
                contract=node.contract_name,
                function_name=node.function_name,
                address=state.instruction["address"],
                swc_id=REENTRANCY,
                title="State write for 1600 gas or less",
                severity="Medium",
                bytecode=state.environment.code.bytecode,
                description_head="Caller can modify state for 1600 gas or less.",
                description_tail="The planned Constantinople hard fork reduces the gas cost for writing to state "
                                 +"variables that have been written to in the same transaction. In some cases "
                                 +"this may cause re-rentrancy vulnerabilities in previously safe contracts.",
                debug=transaction_sequence,
                gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
            )

            return [issue]

    return []


class ConstantinopleReentrancy(DetectionModule):

    def __init__(self):
        """"""
        super().__init__(
            name="Constantinople reentrancy vulnerability",
            swc_id=REENTRANCY,
            description=DESCRIPTION,
            entrypoint="callback",
            pre_hooks=["STOP", "RETURN"],
        )

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """

        self._issues.extend(_analyze_state(state))
        return self.issues


detector = ConstantinopleReentrancy()
