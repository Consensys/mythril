"""This module contains the detection code for potentially insecure low-level
calls."""

from mythril.analysis import solver
from mythril.analysis.swc_data import REENTRANCY
from mythril.analysis.modules.base import DetectionModule
from mythril.analysis.report import Issue
from mythril.laser.smt import UGT, symbol_factory
from mythril.laser.ethereum.state.global_state import GlobalState
from mythril.laser.ethereum.state.annotation import StateAnnotation
from mythril.exceptions import UnsatError
import logging
import json

log = logging.getLogger(__name__)

DESCRIPTION = """

Search for external calls followed by a state change (CALL / SSTORE).

"""

class PostCallAnnotation(StateAnnotation):
    pass


def _analyze_state(state):
    """
     :param state:
     :return:
     """
    node = state.node

    if len(list(state.get_annotations(PostCallAnnotation))) > 0:

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
            title="State change after external call",
            severity="Medium",
            bytecode=state.environment.code.bytecode,
            description_head="State change after external call.",
            description_tail="The contract account state is changed after an external call. Consider that the "
                "called contract could re-enter the function before this state change takes place. This can lead to " 
                "business logic vulnerabilities.",
            debug=transaction_sequence,
            gas_used=(state.mstate.min_gas_used, state.mstate.max_gas_used),
        )

        return [issue]

    elif state.instruction["opcode"] == "CALL":
        state.annotate(PostCallAnnotation())

    return []


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
            pre_hooks=["CALL", "SSTORE"]
        )

    def execute(self, state: GlobalState):
        """

        :param state:
        :return:
        """
        self._issues.extend(_analyze_state(state))
        return self.issues


detector = ExternalCalls()
